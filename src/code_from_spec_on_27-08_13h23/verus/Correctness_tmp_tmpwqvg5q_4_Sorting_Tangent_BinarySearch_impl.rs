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
proof fn lemma_midpoint(low: int, high: int)
    ensures
        low <= high ==> low <= (low + high) / 2 < high + 1
{
    if low <= high {
        assert(low <= (low + high) / 2) by {
            assert(low * 2 <= low + high);
            assert(low * 2 <= 2 * ((low + high) / 2)) by {
                assert(low + high <= 2 * ((low + high) / 2) + 1);
            }
        };
        assert((low + high) / 2 < high + 1) by {
            assert(low + high < high * 2 + 2);
            assert(2 * ((low + high) / 2) <= low + high);
        };
    }
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
fn binary_search(a: &[i32], circle: i32) -> (n: usize)
    requires 
        forall|i: int| #![trigger a[i]] 1 <= i < a.len() ==> a[i-1] < a[i],
        forall|i: int, j: int| #![trigger a[i], a[j]] 0 <= i < j < a.len() ==> a[i] < a[j],
    ensures 
        n <= a.len(),
        forall|i: int| #![trigger a[i]] 0 <= i < n ==> a[i] < circle,
        forall|i: int| #![trigger a[i]] n <= i < a.len() ==> circle <= a[i],
{
    let mut low: usize = 0;
    let mut high: usize = a.len();
    
    while low < high
        invariant
            0 <= low <= high <= a.len(),
            forall|i: int| #![trigger a[i]] 0 <= i < low ==> a[i] < circle,
            forall|i: int| #![trigger a[i]] high <= i < a.len() ==> circle <= a[i],
        decreases high - low
    {
        let mid = (low + high) / 2;
        proof {
            lemma_midpoint(low as int, high as int);
        }
        if a[mid] < circle {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    low
}
// </vc-code>

fn main() {
}

}