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
fn lemma_sorted_array_transitive(a: &[i32], i: int, j: int, k: int)
    requires
        forall|x: int, y: int| #![trigger a[x], a[y]] 0 <= x < y < a.len() ==> a[x] < a[y],
        0 <= i < j < k < a.len(),
    ensures
        a[i] < a[k],
{
}

fn lemma_binary_search_invariant(a: &[i32], circle: i32, low: usize, high: usize)
    requires
        forall|i: int, j: int| #![trigger a[i], a[j]] 0 <= i < j < a.len() ==> a[i] < a[j],
        low <= high,
        high <= a.len(),
        forall|i: int| #![trigger a[i]] 0 <= i < low ==> a[i] < circle,
        forall|i: int| #![trigger a[i]] high <= i < a.len() ==> circle <= a[i],
    ensures
        forall|i: int| #![trigger a[i]] 0 <= i < low ==> a[i] < circle,
        forall|i: int| #![trigger a[i]] high <= i < a.len() ==> circle <= a[i],
{
}
// </vc-helpers>

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
// <vc-code>
{
    let mut low: usize = 0;
    let mut high: usize = a.len();
    
    while low < high
        invariant
            low <= high,
            high <= a.len(),
            forall|i: int| #![trigger a[i]] 0 <= i < low ==> a[i] < circle,
            forall|i: int| #![trigger a[i]] high <= i < a.len() ==> circle <= a[i],
            forall|i: int, j: int| #![trigger a[i], a[j]] 0 <= i < j < a.len() ==> a[i] < a[j],
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        assert(low <= mid < high);
        
        if a[mid] < circle {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    
    assert(low == high);
    low
}
// </vc-code>

fn main() {
}

}