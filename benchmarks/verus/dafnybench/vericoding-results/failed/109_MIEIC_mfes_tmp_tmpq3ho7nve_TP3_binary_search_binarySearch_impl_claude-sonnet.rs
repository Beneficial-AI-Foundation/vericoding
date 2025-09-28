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
// Helper lemma to establish that if x is not in the remaining search space,
// then x is not in the entire array
proof fn lemma_not_found(a: &[i32], x: i32, low: usize, high: usize)
    requires 
        is_sorted(a),
        low <= a.len(),
        high < a.len(),
        low > high,
        forall|k: int| 0 <= k < low ==> a[k] < x,
        forall|k: int| high < k < a.len() ==> a[k] > x
    ensures !a@.contains(x)
{
    if a@.contains(x) {
        let idx = choose|i: int| 0 <= i < a.len() && a[i] == x;
        if idx < low {
            assert(a[idx] < x);
            assert(a[idx] == x);
            assert(false);
        } else if idx > high {
            assert(a[idx] > x);
            assert(a[idx] == x);
            assert(false);
        } else {
            assert(low <= idx <= high);
            assert(low > high);
            assert(false);
        }
    }
}

// Helper lemma for when we break due to boundary conditions
proof fn lemma_boundary_not_found(a: &[i32], x: i32)
    requires 
        is_sorted(a),
        a.len() > 0,
        (a[0] > x || a[a.len() - 1] < x)
    ensures !a@.contains(x)
{
    if a@.contains(x) {
        let idx = choose|i: int| 0 <= i < a.len() && a[i] == x;
        if a[0] > x {
            assert(a[0] <= a[idx]);
            assert(a[0] > x);
            assert(a[idx] == x);
            assert(false);
        } else {
            assert(a[idx] <= a[a.len() - 1]);
            assert(a[a.len() - 1] < x);
            assert(a[idx] == x);
            assert(false);
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
    if a.len() == 0 {
        return -1;
    }
    
    let mut low: usize = 0;
    let mut high: usize = a.len() - 1;
    
    while low <= high
        invariant 
            0 <= low <= a.len(),
            high < a.len(),
            is_sorted(a),
            forall|k: int| 0 <= k < low ==> a[k] < x,
            forall|k: int| high < k < a.len() ==> a[k] > x,
            // Additional invariant to help prove postcondition
            forall|k: int| 0 <= k < a.len() && a[k] == x ==> low <= k <= high
        decreases high + 1 - low
    {
        let mid = low + (high - low) / 2;
        
        assert(low <= mid <= high);
        assert(mid < a.len());
        
        if a[mid] == x {
            assert(0 <= mid < a.len());
            assert(mid < a.len() <= usize::MAX);
            assert(mid <= i32::MAX);
            return mid as i32;
        } else if a[mid] < x {
            if mid == a.len() - 1 {
                proof {
                    lemma_boundary_not_found(a, x);
                }
                return -1;
            }
            // Prove that all elements from low to mid are < x
            assert(forall|k: int| low <= k <= mid ==> a[k] <= a[mid as int]);
            assert(forall|k: int| low <= k <= mid ==> a[k] < x);
            low = mid + 1;
        } else {
            if mid == 0 {
                proof {
                    lemma_boundary_not_found(a, x);
                }
                return -1;
            }
            // Prove that all elements from mid to high are > x
            assert(forall|k: int| mid <= k <= high ==> a[mid as int] <= a[k]);
            assert(forall|k: int| mid <= k <= high ==> a[k] > x);
            high = mid - 1;
        }
    }
    
    // At this point, low > high, so x is not in the array
    proof {
        lemma_not_found(a, x, low, high);
    }
    
    -1
}
// </vc-code>

fn main() {
}

}