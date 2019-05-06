// Note: PriorityQueue is 3x faster than C++, likely due the lack of generality; this is
// strictly a 'MIN' heap only defined by the partial relation '<'.

class PriorityQueue {
    type eltType;
	var dom = {0..1024};
	var arr : [dom] eltType;
	var size : int;

	proc init(type eltType) {
		this.eltType = eltType;
	}
	
	proc isEmpty return size == 0;

	proc add(elt : eltType) : bool {
		on this {
			var idx = size;
        			
			// Resize if needed
			if idx >= dom.last {
				dom = {0..(((dom.last * 1.5) : int) - 1)};
			}

			// Insert
			arr[idx] = elt;
			size += 1;

			// Rebalance
			if idx > 0 {
				var child = arr[idx];
				var parent = arr[getParent(idx)];

				// Heapify Up
				while idx != 0 && parent > child {
					var tmp = arr[idx];
					arr[idx] = arr[getParent(idx)];
					arr[getParent(idx)] = tmp;

					idx = getParent(idx);
					child = arr[idx];
					parent = arr[getParent(idx)];
				}
			}
		}
		return true;
	}

	// Implement Collection's 'remove' 
	proc remove() : (bool, eltType) {
		var retval : (bool, eltType);
      	on this {
      		if size > 0 {
				retval =  (true, arr[0]);
				arr[0] = arr[size - 1];
				size -= 1;

				heapify(0);
			}
      	}
      	return retval;
	}

	proc heapify(_idx : int) {
		var idx = _idx;
		if size <= 1 {
			return;
		}

		var l = getLeft(idx);
		var r = getRight(idx);
		var tmp = idx;
		var curr = arr[idx];

		// left > current
		if size > l && arr[l] < curr {
			curr = arr[l];
			idx = l;
		}

		// right > current
		if size > r && arr[r] < curr {
			curr = arr[r];
			idx = r;
		}

		if idx != tmp {
			var swapTmp = arr[tmp];
			arr[tmp] = arr[idx];
			arr[idx] = swapTmp;

			heapify(idx);
		}
	}

	inline proc getParent(x:int) : int {
		return floor((x - 1) / 2) : int;
	}

	inline proc getLeft(x:int) : int {
		return 2 * x + 1; 
	}

	inline proc getRight(x:int) : int {
		return 2 * x + 2;
	}
}

use Random;
use Sort;
use Time;

proc main() { 
    var timer = new Timer();
	const nElems = 1024 * 1024;
	var pq = new PriorityQueue(int);

	// Generate random elems
	var rng = makeRandomStream(int);
	var arr : [1..nElems] int;
	rng.fillRandom(arr);

	// Test Collection's 'addBulk' utility method
	timer.start();
    for a in arr do pq.add(a);

	// Test Collection's 'removeBulk'
	var sortedArr = for i in 1..nElems do pq.remove();
    timer.stop();

	// Test Collection's 'removeBulk'

	// Test result...
	var cmp2 = new DefaultComparator();
	assert(isSorted(sortedArr, cmp2));

    writeln("NumOps: ", nElems, " Time: ", timer.elapsed());
}
