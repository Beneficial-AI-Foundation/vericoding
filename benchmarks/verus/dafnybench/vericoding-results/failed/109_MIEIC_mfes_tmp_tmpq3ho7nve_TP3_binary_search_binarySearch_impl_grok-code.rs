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
spec fn is_sorted(a: &[i32]) -> bool {
    forall|i: int, j: int| 0 <= i < j < a@.len() ==> #[trigger(a@[i])] a@[i] <= a@[j]
}
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
    let mut low: usize = 0;
    let mut high: usize = if a@.len() == 0 { 0 } else { (a@.len() as usize) - 1 };
    while low <= high
        invariant
            is_sorted(a),
            0 <= low <= high + 1 <= a@.len(),
            forall|j: usize| 0 <= j < low ==> #[trigger(a@[j as int])] a@[j as int] != x,
            forall|j: usize| high < j <= a@.len() - 1 ==> #[trigger(a@[j as int])] a@[j as int] != x,
        decreases high - low + 1,
    {
        let mid: usize = low + (high - low) / 2;
        if a@[mid as int] < x {
            assert(forall|k: usize| k < mid ==> #[trigger(a@[k as int])] a@[k as int] < x);
            assert(forall|j: usize| 0 <= j < low ==> #[trigger(a@[j as int])] a@[j as int] != x);
            low = mid + 1;
        } else if a@[mid as int] > x {
            assert(forall|k: usize| mid < k <= a@.len() - 1 ==> #[trigger(a@[k as int])] a@[k as int] > x);
            assert(forall|j: usize| high < j < a@.len() ==> #[trigger(a@[j as int])] a@[j as int] != x);
            high = mid - 1;
        } else {
            return mid as i32;
        }
    }
    return -1;
}
// </vc-code>

fn main() {
}

}