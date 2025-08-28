use vstd::prelude::*;

verus! {

/**
  Ather, Mohammad Faiz (s4648481/3)
  CSSE3100
  Assignemnt 3
  The University of Queensland
 */

// Question 1

// Author: Leino, Title: Program Proofs

// <vc-helpers>
// Helper lemmas for binary search verification
proof fn lemma_sorted_transitive(a: &[i32], i: int, j: int, k: int)
    requires
        forall|x: int, y: int| #![trigger a[x], a[y]] 0 <= x < y < a.len() ==> a[x] < a[y],
        0 <= i < j < k < a.len(),
    ensures
        a[i] < a[j] && a[j] < a[k] && a[i] < a[k]
{
}

proof fn lemma_partition_invariant(a: &[i32], circle: i32, low: usize, high: usize, mid: usize)
    requires
        forall|i: int, j: int| #![trigger a[i], a[j]] 0 <= i < j < a.len() ==> a[i] < a[j],
        low <= mid < high,
        high <= a.len(),
        forall|i: int| #![trigger a[i]] 0 <= i < low ==> a[i] < circle,
        forall|i: int| #![trigger a[i]] high <= i < a.len() ==> circle <= a[i],
    ensures
        mid < a.len(),
        (a[mid as int] < circle ==> forall|i: int| #![trigger a[i]] 0 <= i <= mid ==> a[i] < circle),
        (circle <= a[mid as int] ==> forall|i: int| #![trigger a[i]] mid <= i < a.len() ==> circle <= a[i]),
{
    // The sorted property ensures the partition property holds
    assert(mid < high <= a.len());
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn binary_search(a: &[i32], circle: i32) -> (n: usize)
    requires 
        forall|i: int| #![trigger a[i]] 1 <= i < a.len() ==> a[i-1] < a[i],
        forall|i: int, j: int| #![trigger a[i], a[j]] 0 <= i < j < a.len() ==> a[i] < a[j],
    ensures 
        n <= a.len(),
        forall|i: int| #![trigger a[i]] 0 <= i < n ==> a[i] < circle,
        forall|i: int| #![trigger a[i]] n <= i < a.len() ==> circle <= a[i],
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut low = 0;
    let mut high = a.len();
    
    while low < high
        invariant
            low <= high <= a.len(),
            forall|i: int| #![trigger a[i]] 0 <= i < low ==> a[i] < circle,
            forall|i: int| #![trigger a[i]] high <= i < a.len() ==> circle <= a[i],
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        assert(low <= mid < high);
        
        if a[mid] < circle {
            proof {
                assert(forall|i: int, j: int| #![trigger a[i], a[j]] 0 <= i < j < a.len() ==> a[i] < a[j]);
                assert(low <= mid < high);
                assert(high <= a.len());
                lemma_partition_invariant(a, circle, low, high, mid);
            }
            low = mid + 1;
        } else {
            proof {
                assert(forall|i: int, j: int| #![trigger a[i], a[j]] 0 <= i < j < a.len() ==> a[i] < a[j]);
                assert(low <= mid < high);
                assert(high <= a.len());
                lemma_partition_invariant(a, circle, low, high, mid);
            }
            high = mid;
        }
    }
    
    low
}
// </vc-code>

fn main() {
}

}