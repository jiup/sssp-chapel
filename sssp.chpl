use Time;
use Sort;
use pqueue;

/*
    Document on Lifetime Checking: https://chapel-lang.org/docs/master/technotes/lifetimeChecking.html

    Quick Language Reference: https://chapel-lang.org/docs/master/_downloads/quickReference.pdf 

    Note: Explicitly using 'unmanaged' lifetimes over 'borrowed' in certain contexts as there is a bug where the compiler
    cannot accurately deduce the lifetime of a scoped variable frm iterators. The 'unmanaged' lifetime 
    is equivalent to the 'borrowed' lifetime without the compile-time checking. Chapel Issue #12599 
    https://github.com/chapel-lang/chapel/issues/12599

*/

// Compile-time constant
param unreached : real(64) = INFINITY;

// Can be set via command line: './dijkstra --graphFile=graph.txt'
config const graphFile : string = "graphs/graph10";
config const fixedDelta : real(64) = NAN;
config const fixedNumBuckets : int(64) = 0;

class Vertex {
    // Synchronize access when relaxing...
    var relaxLock$ : sync bool;
    var id : int(64);
    var distance : real(64);
    var incidentDom = {0..-1};
    var incident : [incidentDom] borrowed Edge;

    proc init(id : integral, distance = unreached) {
        this.id = id : int(64);
        this.distance = distance;
    }

    // Returns edges this vertex is incident in that
    // is greater than delta.
    iter heavy(delta : real(64)) : (borrowed Edge) {
        for e in incident {
            if e.weight > delta {
                yield e;
            }
        }
    }

    iter heavy(param tag : iterKind, delta : real(64)) : (borrowed Edge) where tag == iterKind.standalone {
        forall e in incident {
            if e.weight > delta {
                yield e;
            }
        }
    }

    // Returns edges this vertex is incident in that
    // is less than or equal to delta.
    iter light(delta : real(64)) : (borrowed Edge) {
        for e in incident {
            if e.weight <= delta {
                yield e;
            }
        }
    }

    iter light(param tag : iterKind, delta : real(64)) : (borrowed Edge) where tag == iterKind.standalone {
        forall e in incident {
            if e.weight <= delta {
                yield e;
            }
        }
    }

    // Return adjacent neighbors... A vertex 'v' is
    // adjacent to a vertex 'u' if it is incident in an
    // edge '(v,u)'.
    iter neighbors() : (real(64), borrowed Vertex) {
        for e in incident {
            if e.v1 == this {
                yield (e.weight, e.v2);
            } else if e.v2 == this {
                yield (e.weight, e.v1);
            } else {
                halt("An edge ", e, " does not contain vertex ", this, " even though we are incident in it!");
            }
        }
    }

    // Parallel Iterator Example; the parallel iterator for 'incident', a Chapel array, is used as the backbone.
    // 'forall' results in this parallel iterator being selected, while 'for' results in the above serial iterator
    // being selected. 
    // https://chapel-lang.org/docs/master/primers/parIters.html#primers-pariters
    iter neighbors(param tag : iterKind) : (real(64), borrowed Vertex) where tag == iterKind.standalone {
        forall e in incident {
            if e.v1 == this {
                yield (e.weight, e.v2);
            } else if e.v2 == this {
                yield (e.weight, e.v1);
            } else {
                halt("An edge ", e, " does not contain vertex ", this, " even though we are incident in it!");
            }
        }
    }

    proc readWriteThis(f) {
        f   <~> new ioLiteral("Vertex(") 
            <~> this.id 
            <~> new ioLiteral(",") 
            <~> this.distance 
            <~> new ioLiteral(")");
    }
}

//
// Overloads operators; needed for priority queue.
//

proc >(v1 : Vertex, v2 : Vertex) {
    return v1.distance > v2.distance;
}

proc <(v1 : Vertex, v2 : Vertex) {
    return v1.distance < v2.distance;
}


// Associative domain acts as a set.
// https://chapel-lang.org/docs/master/technotes/sets.html
type bucketType = domain(Vertex);

class Edge {
    var v1 : borrowed Vertex;
    var v2 : borrowed Vertex;
    var weight : real(64);

    proc init(v1 : borrowed Vertex, v2 : borrowed Vertex, weight : real(64)) {
        this.v1 = v1;
        this.v2 = v2;
        this.weight = weight;
    }

    proc other(v : borrowed Vertex) : borrowed Vertex {
        if this.v1 == v {
            return this.v2;
        } else if this.v2 == v {
            return this.v1;
        } else {
            halt("Vertex ", v, " not included in an edge that it is incident on...");
        }
    }

    proc readWriteThis(f) {
        f   <~> new ioLiteral("Edge(") 
            <~> this.v1 
            <~> new ioLiteral(",") 
            <~> this.v2 
            <~> new ioLiteral(",")
            <~> this.weight
            <~> new ioLiteral(")");
    }

    // Alias for the weight; provided to enhance intuition for how algorithm works.
    proc cost return this.weight;
}

class Graph {
    var vertexDom = {0..-1};
    var edgeDom = {0..-1};
    var vertices : [vertexDom] owned Vertex;
    var edges : [edgeDom] owned Edge;

    proc init() {}

    // Adds a vertex to the graph; this transfers ownership!
    proc addVertex(v : owned Vertex) {
        this.vertices.push_back(v);
    }

    // Adds an edge to the graph; this transfers ownership
    proc addEdge(e : owned Edge) {
        e.v1.incident.push_back(e);
        e.v2.incident.push_back(e);
        this.edges.push_back(e);
    }

    // vertex = Graph[idx]; 
    proc this(idx : integral) : borrowed Vertex {
        return this.vertices[idx];
    }

    // After calls to addVertex, call this to sort the vertices by their
    // id so that they can be obtained via indexing by said id.
    proc __finishInit() {
        // Chapel sort comparator; sorts vertices via vertex id.
        // https://chapel-lang.org/docs/master/modules/packages/Sort.html#comparators
        record VertexIDCMP {
            proc key(v : borrowed Vertex) return v.id;
        }
        sort(this.vertices, new VertexIDCMP());
    }

    proc readWriteThis(f) {
        f   <~> new ioLiteral("Graph(") 
            <~> this.vertices 
            <~> new ioLiteral(",") 
            <~> this.edges 
            <~> new ioLiteral(")");
    }
}

proc loadGraph(fileName : string) : owned Graph {
    var graph = new owned Graph();
    var freader = open(fileName, iomode.r).reader();
    
    // Read header...
    var numVertices : int(64);
    var numEdges : int(64);
    // |V| |E|
    assert(freader.readln(numVertices, numEdges));

    // Allocate all vertices...
    for i in 0..#numVertices {
        graph.addVertex(new owned Vertex(i));
    }
    graph.__finishInit();

    // Extract edges...
    var v1 : int(64);
    var v2 : int(64);
    var weight : real(64);
    while (freader.readln(v1, v2, weight)) {
        graph.addEdge(new owned Edge(graph[v1], graph[v2], weight));
    }

    return graph;
}

// Relaxes the distance of a vertex. 
// Sets the distance if unreached or less than current distance.
// Also moves the vertex to a new bucket if it is different.
proc relax(vertex : borrowed Vertex, dist : real(64), delta : real(64), buckets : [?bucketDom] bucketType) {
    vertex.relaxLock$ = true;
    if dist < vertex.distance {
        if !isinf(vertex.distance) {
            const oldBucket = floor((vertex.distance / delta)) : int(64) % bucketDom.size;
            buckets[oldBucket] -= vertex;
        }

        const newBucket = floor((dist / delta)) : int(64) % bucketDom.size;
        vertex.distance = dist;
        buckets[newBucket] += vertex;
    }
    vertex.relaxLock$;
}

// Hint: Parallelize this...
iter gatherLightRequests(bucket : bucketType, delta : real(64)) : (unmanaged Vertex, real(64)) {
    for v in bucket {
        for e in v.light(delta) {
            yield (e.other(v) : unmanaged, v.distance + e.cost);
        }
    }
}

iter gatherLightRequests(param tag : iterKind, bucket : bucketType, delta : real(64)) : (unmanaged Vertex, real(64)) where tag == iterKind.standalone {
    forall v in bucket {
        forall e in v.light(delta) {
            yield (e.other(v) : unmanaged, v.distance + e.cost);
        }
    }
}

// Hint: Parallelize this...
iter gatherHeavyRequests(bucket : bucketType, delta : real(64)) : (unmanaged Vertex, real(64)) {
    for v in bucket {
        for e in v.heavy(delta) {
            yield (e.other(v) : unmanaged, v.distance + e.cost);
        }
    }
}

iter gatherHeavyRequests(param tag : iterKind, bucket : bucketType, delta : real(64)) : (unmanaged Vertex, real(64)) where tag == iterKind.standalone{
    forall v in bucket {
        forall e in v.heavy(delta) {
            yield (e.other(v) : unmanaged, v.distance + e.cost);
        }
    }
}

proc DeltaStepping(graph : borrowed Graph, source : borrowed Vertex) {
    // Max edge weight
    const maxEdgeWeight : real(64) = max reduce [e in graph.edges] e.weight;
    // Max degree 'd'
    const degree : int(64) =  max reduce [v in graph.vertices] v.incident.size;
    const delta : real(64) = if !isnan(fixedDelta) then fixedDelta else 1 / (degree : real(64));
    const numBuckets : int(64) = if fixedNumBuckets > 0 then fixedNumBuckets else floor((maxEdgeWeight / delta) + 1) : int(64);

    writeln("Metrics: maxEdgeWeight = ", maxEdgeWeight, ", degree = ", degree, ", delta = ", delta, ", numBuckets = ", numBuckets);
    const bucketsDom = {0..#numBuckets};
    var buckets : [bucketsDom] bucketType;

    relax(source, 0, delta, buckets);
    buckets[0] += source;
    var bucketIdx = 0;
    label bucketsNotEmpty
    while true {
        // We revisit vertices we have already processed to handle
        // the cases where vertices are connected to edges that
        // have weights greater than delta.
        var verticesProcessed : bucketType;

        // Need to gather all potential edges with a distance <= delta
        while (buckets[bucketIdx].size != 0) {
            var oldBucket = buckets[bucketIdx];
            verticesProcessed += buckets[bucketIdx];
            buckets[bucketIdx].clear();

            forall (v, newDist) in  gatherLightRequests(oldBucket, delta) {
                relax(v, newDist, delta, buckets);
            }
        }

        forall (v, dist) in gatherHeavyRequests(verticesProcessed, delta) {
            relax(v, dist, delta, buckets);
        }

        // Find first non-empty bucket...
        var currBucketIdx : bucketIdx.type;
        for i in bucketsDom {
            if buckets[i].size != 0 {
                bucketIdx = i;
                continue bucketsNotEmpty;
            }
        }
        break bucketsNotEmpty;
    }
}

proc Dijkstra(graph : borrowed Graph, source : borrowed Vertex) {
    var pq = new PriorityQueue((real(64), borrowed Vertex));
    source.distance = 0;

    pq.add((source.distance, source));
    while (!pq.isEmpty) {
        var (hasElt, elt) = pq.remove();
        assert(hasElt, "Priority Queue is not being empty but no element was returned...");
        var (dist, v) = elt;
        if (dist != v.distance) {
            continue;
        }

        for (weight, neighbor) in v.neighbors() {
            var altDist = v.distance + weight;
            
            if (isnan(neighbor.distance) || altDist < neighbor.distance) {
                neighbor.distance = altDist;
                pq.add((altDist, neighbor));
            }
        }
    }
}

proc main() {
    var timer = new Timer();
    var graph = loadGraph(graphFile);
    timer.start();
    Dijkstra(graph, graph.vertices[0]);
    timer.stop();
    writeln("Dijkstra = ", timer.elapsed());
    var maximalSSSP : (real(64), int(64));
    var expectedDistance : [graph.vertexDom] real(64);
    forall (v, dist) in zip(graph.vertices, expectedDistance) with (max reduce maximalSSSP) {
        dist = v.distance;
        maximalSSSP = max(maximalSSSP, (v.distance, v.id));
        v.distance = unreached;
    }
    writeln("Maximal Shortest Path is between #0 and #", maximalSSSP[2], " = ", maximalSSSP[1]);
    
    timer.clear();
    timer.start();
    DeltaStepping(graph, graph.vertices[0]);
    timer.stop();
    writeln("Delta Stepping = ", timer.elapsed());
    for (v, dist) in zip(graph.vertices, expectedDistance) {
        assert(v.distance == dist);
    }
}
