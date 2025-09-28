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
// Helper lemma: if x < a[mid] in a sorted array, then x is not in [mid, high)
proof fn lemma_not_in_right_half(a: &[i32], x: i32, low: int, mid: int, high: int)
    requires
        is_sorted(a),
        0 <= low <= mid < high <= a.len(),
        x < a[mid],
    ensures
        forall|i: int| mid <= i < high ==> a[i] != x,
{
    assert forall|i: int| mid <= i < high implies a[i] != x by {
        if i == mid {
            // x < a[mid], so a[i] != x
        } else {
            // i > mid, and since array is sorted, a[mid] <= a[i]
            // Since x < a[mid] <= a[i], we have x < a[i], so a[i] != x
            assert(a[mid] <= a[i]);
        }
    }
}

// Helper lemma: if x > a[mid] in a sorted array, then x is not in [low, mid+1)
proof fn lemma_not_in_left_half(a: &[i32], x: i32, low: int, mid: int, high: int)
    requires
        is_sorted(a),
        0 <= low <= mid < high <= a.len(),
        x > a[mid],
    ensures
        forall|i: int| low <= i <= mid ==> a[i] != x,
{
    assert forall|i: int| low <= i <= mid implies a[i] != x by {
        if i == mid {
            // x > a[mid], so a[i] != x
        } else {
            // i < mid, and since array is sorted, a[i] <= a[mid]
            // Since x > a[mid] >= a[i], we have x > a[i], so a[i] != x
            assert(a[i] <= a[mid]);
        }
    }
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
    if a.len() >= i32::MAX as usize {
        return -1;
    }
    
    let mut low: usize = 0;
    let mut high: usize = a.len();
    
    while low < high
        invariant
            0 <= low <= high <= a.len(),
            a.len() < i32::MAX as usize,
            is_sorted(a),
            forall|i: int| 0 <= i < low ==> a[i] != x,
            forall|i: int| high <= i < a.len() ==> a[i] != x,
        decreases high - low,
    {
        let mid: usize = low + (high - low) / 2;
        assert(low <= mid < high);
        
        if a[mid as usize] == x {
            assert(0 <= mid < a.len());
            assert(a[mid as int] == x);
            assert(mid < i32::MAX as usize) by {
                assert(mid < a.len());
                assert(a.len() < i32::MAX as usize);
            }
            let result: i32 = mid as i32;
            assert(-1 <= result < a.len());
            assert(a[result as int] == x);
            return result;
        } else if x < a[mid as usize] {
            proof {
                lemma_not_in_right_half(a, x, low as int, mid as int, high as int);
                assert forall|i: int| high <= i < a.len() implies a[i] != x by {}
                assert forall|i: int| mid <= i < a.len() implies a[i] != x by {
                    if i < high {
                        // From lemma_not_in_right_half
                    } else {
                        // From loop invariant
                    }
                }
            }
            high = mid;
        } else {
            proof {
                lemma_not_in_left_half(a, x, low as int, mid as int, high as int);
                assert forall|i: int| 0 <= i < low implies a[i] != x by {}
                assert forall|i: int| 0 <= i <= mid implies a[i] != x by {
                    if i < low {
                        // From loop invariant
                    } else {
                        // From lemma_not_in_left_half
                    }
                }
            }
            low = mid + 1;
        }
    }
    
    assert(low == high);
    assert(forall|i: int| 0 <= i < a.len() ==> a[i] != x);
    assert(!a@.contains(x));
    -1
}
// </vc-code>

fn main() {
}

}