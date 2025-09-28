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
fn contains_at_index(s: Seq<i32>, x: i32, start: int, end: int) -> bool {
    // Helper function to check if an element 'x' is present in a sub-sequence of 's'
    // from 'start' to 'end' (exclusive of end).
    // This is useful for the post-condition when x is not found.
    forall|i: int| start <= i < end ==> s[i] == x
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
    let mut low: int = 0;
    let mut high: int = a.len() as int; // exclusive upper bound

    while low < high
        invariant
            0 <= low <= high <= a.len(),
            // a: Seq<i32> from slice
            is_sorted(a), // Array remains sorted throughout
            // If x exists in the original array, it must be in a[low..high]
            // This is crucial for proving the post-condition when x is found
            forall|i: int| #![trigger a[i]] 0 <= i < a.len() ==> (a[i] == x ==> (low <= i < high)),
            // If x is NOT in a[0..low], it won't be in the final found range
            // Also crucial for proving the post-condition when x is NOT found
            forall|i: int| #![trigger a[i]] 0 <= i < low ==> a[i] != x,
            // If x is NOT in a[high..a.len()], it won't be in the final found range
            forall|i: int| #![trigger a[i]] high <= i < a.len() ==> a[i] != x,
    decreases high - low
    {
        let mid: int = low + (high - low) / 2;

        if a[mid as nat] == x {
            return mid as i32;
        } else if a[mid as nat] < x {
            // x is in the upper half (if it exists)
            // Anything from low to mid (inclusive) cannot be x
            // because a[i] <= a[mid] < x for all i <= mid
            proof {
                assert(is_sorted(a));
                assert forall|i: int| 0 <= i < low implies a[i] != x by {
                    // This part of invariant holds by loop invariant
                }
                assert forall|i: int| low <= i <= mid implies a[i] < x by {
                    assert(a[mid as nat] < x);
                    assert(is_sorted(a));
                    if low <= i <= mid {
                        assert(a[i] <= a[mid as nat]);
                        assert(a[i] < x);
                    }
                }
                assert forall|i: int| 0 <= i < mid + 1 implies a[i] != x by {
                    if 0 <= i && i < low {
                        assert(a[i] != x); // from existing invariant
                    } else if low <= i && i <= mid {
                        assert(a[i] < x); // proven in this step
                    }
                }
            }
            low = mid + 1;
        } else { // a[mid as nat] > x
            // x must be in the lower half (if it exists)
            // Anything from mid to high (exclusive) cannot be x
            // because a[mid] > x and a[mid] <= a[i] for all i >= mid
            proof {
                assert(is_sorted(a));
                assert forall|i: int| high <= i < a.len() implies a[i] != x by {
                    // This part of invariant holds by loop invariant
                }
                assert forall|i: int| mid <= i < high implies a[i] > x by {
                    assert(a[mid as nat] > x);
                    assert(is_sorted(a));
                    if mid <= i && i < high {
                        assert(a[mid as nat] <= a[i]);
                        assert(a[i] > x);
                    }
                }
                assert forall|i: int| mid <= i < a.len() implies a[i] != x by {
                    if mid <= i && i < high {
                        assert(a[i] > x); // proven in this step
                    } else if high <= i && i < a.len() {
                        assert(a[i] != x); // from existing invariant
                    }
                }
            }
            high = mid;
        }
    }

    // After the loop, low == high.
    // The invariant implies that if x existed in the original array,
    // it must be in the range [low, high), which is now empty.
    // Therefore, x is not in the array.
    proof {
        assert(low == high);
        assert forall|i: int| 0 <= i < a.len() implies (a[i] == x ==> (low <= i && i < high)) by {
            // This is directly from the loop invariant
        }
        assert forall|i: int| 0 <= i < a.len() implies (a[i] == x ==> (i < low || i >= high)); // derived from [low, high) being empty
        assert forall|i: int| 0 <= i < low implies a[i] != x;
        assert forall|i: int| high <= i < a.len() implies a[i] != x;

        assert forall|i: int| 0 <= i < a.len() implies a[i] != x by {
            if 0 <= i && i < low {
                assert(a[i] != x);
            } else if low <= i && i < high {
                // This range is empty because low == high
                assert(false); // Contradiction: This branch should not be reached
            } else if high <= i && i < a.len() {
                assert(a[i] != x);
            } else {
                assert(false);
            }
        };

        // This proves that #a@.contains(x) is false
        // Therefore, we can conclude that the post-condition for index == -1 is satisfied.
    }
    -1
}
// </vc-code>

fn main() {
}

}