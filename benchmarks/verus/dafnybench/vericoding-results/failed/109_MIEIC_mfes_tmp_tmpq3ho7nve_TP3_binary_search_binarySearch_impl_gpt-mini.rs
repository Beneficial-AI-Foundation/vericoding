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
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
fn binary_search(a: &[i32], x: i32) -> (index: i32)
    requires is_sorted(a)
    ensures -1 <= index < a.len() && 
            (index != -1 ==> a[index as int] == x) &&
            (index == -1 ==> !a@.contains(x))
// </vc-spec>
// <vc-code>
{
    let mut low: nat = 0;
    let mut high: nat = a.len() as nat;
    while low < high
        invariant low <= high;
        invariant high <= a.len() as nat;
        invariant forall|i: int| 0 <= i && i < a.len() as int && (i < low as int || i >= high as int) ==> a@[i] != x;
        decreases high - low;
    {
        let mid: nat = (low + high) / 2;
        assert(mid < a.len() as nat);
        let v = a[mid as usize];
        if v < x {
            low = mid + 1;
        } else if v > x {
            high = mid;
        } else {
            return mid as i32;
        }
    }
    assert(low == high);
    assert(forall|i: int| 0 <= i && i < a.len() as int ==> a@[i] != x);
    -1 as i32
}
// </vc-code>

fn main() {
}

}