use vstd::prelude::*;

verus! {

// Checks if array 'a' is sorted.
spec fn is_sorted(a: &[i32]) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
}

// Finds a value 'x' in a sorted array 'a', and returns its index,
// or -1 if not found.

// Simple test cases to check the post-condition.

/*
a) Identify adequate pre and post-conditions for this method, 
and encode them as "requires" and "ensures" clauses in Verus. 
You can use the predicate below if needed.

b) Identify an adequate loop variant and loop invariant, and encode them 
as "decreases" and "invariant" clauses in Verus.
*/

// <vc-helpers>
spec fn all_less_than(a: &[i32], val: i32, end: int) -> bool {
    forall|k: int| 0 <= k < end ==> a[k] < val
}

spec fn all_greater_than(a: &[i32], val: i32, start: int) -> bool {
    forall|k: int| start <= k < a.len() ==> a[k] > val
}

proof fn sorted_implies_bounds(a: &[i32], x: i32, low: int, high: int)
    requires 
        is_sorted(a),
        0 <= low <= high <= a.len(),
        all_less_than(a, x, low),
        all_greater_than(a, x, high)
    ensures !a@.contains(x)
{
    if a@.contains(x) {
        let i = choose|i: int| 0 <= i < a.len() && a[i] == x;
        if i < low {
            assert(a[i] < x);
            assert(a[i] == x);
        } else if i >= high {
            assert(a[i] > x);
            assert(a[i] == x);
        }
    }
}

proof fn mid_in_bounds_proof(mid: usize, len: usize)
    requires mid < len, len <= usize::MAX, len <= i32::MAX as usize
    ensures mid < i32::MAX as usize, mid as i32 >= 0
{
    assert(mid < len <= i32::MAX as usize);
    assert(mid < i32::MAX as usize);
    assert(mid as i32 >= 0);
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn binary_search(a: &[i32], x: i32) -> (index: i32)
    requires is_sorted(a)
    ensures -1 <= index < a.len() && 
            (index != -1 ==> a[index as int] == x) &&
            (index == -1 ==> !a@.contains(x))
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if a.len() > i32::MAX as usize {
        return -1;
    }
    
    let mut low: usize = 0;
    let mut high: usize = a.len();
    
    while low < high
        invariant 
            low <= high <= a.len(),
            all_less_than(a, x, low as int),
            all_greater_than(a, x, high as int),
            is_sorted(a),
            a.len() <= i32::MAX as usize
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        
        if a[mid] == x {
            proof {
                mid_in_bounds_proof(mid, a.len());
            }
            return mid as i32;
        } else if a[mid] < x {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    
    proof {
        sorted_implies_bounds(a, x, low as int, high as int);
    }
    
    -1
}
// </vc-code>

fn main() {
}

}