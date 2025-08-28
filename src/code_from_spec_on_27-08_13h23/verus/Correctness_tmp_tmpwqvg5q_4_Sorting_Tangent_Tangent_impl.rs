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
fn binary_search(a: &[int], circle: int) -> (n: usize)
    requires
        forall|i: int| 1 <= i < a.len() ==> a[i-1] < #[trigger] a[i],
        forall|i: int, j: int| 0 <= i < j < a.len() ==> #[trigger] a[i] < #[trigger] a[j],
    ensures
        n <= a.len(),
        forall|i: int| 0 <= i < n ==> #[trigger] a[i] < circle,
        forall|i: int| n <= i < a.len() ==> circle <= #[trigger] a[i],
{
    assume(false);
    0
}

// <vc-helpers>
proof fn lemma_binary_search_correct(a: &[int], circle: int, n: usize)
    requires
        forall|i: int| 1 <= i < a.len() ==> a[i-1] < #[trigger] a[i],
        forall|i: int, j: int| 0 <= i < j < a.len() ==> #[trigger] a[i] < #[trigger] a[j],
        n <= a.len(),
        forall|i: int| 0 <= i < n ==> #[trigger] a[i] < circle,
        forall|i: int| n <= i < a.len() ==> circle <= #[trigger] a[i],
    ensures
        true,
{
}

fn binary_search(a: &[int], circle: int) -> (n: usize)
    requires
        forall|i: int| 1 <= i < a.len() ==> a[i-1] < #[trigger] a[i],
        forall|i: int, j: int| 0 <= i < j < a.len() ==> #[trigger] a[i] < #[trigger] a[j],
    ensures
        n <= a.len(),
        forall|i: int| 0 <= i < n ==> #[trigger] a[i] < circle,
        forall|i: int| n <= i < a.len() ==> circle <= #[trigger] a[i],
{
    let mut low: usize = 0;
    let mut high: usize = a.len();
    
    while low < high
        invariant
            0 <= low <= high <= a.len(),
            forall|i: int| 0 <= i < low ==> #[trigger] a[i] < circle,
            forall|i: int| high <= i < a.len() ==> circle <= #[trigger] a[i],
    {
        let mid: usize = low + (high - low) / 2;
        if a[mid] < circle {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    low
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn tangent(r: &[int], x: &[int]) -> (found: bool)
    requires
        forall|i: int| 1 <= i < x.len() ==> x[i-1] < #[trigger] x[i],
        forall|i: int, j: int| 0 <= i < j < x.len() ==> #[trigger] x[i] < #[trigger] x[j],
    ensures
        !found ==> forall|i: int, j: int| 
            0 <= i < r.len() && 0 <= j < x.len() ==> #[trigger] r[i] != #[trigger] x[j],
        found ==> exists|i: int, j: int|
            0 <= i < r.len() && 0 <= j < x.len() && #[trigger] r[i] == #[trigger] x[j],
// </vc-spec>
// </vc-spec>

// <vc-code>
fn tangent(r: &[int], x: &[int]) -> (found: bool)
    requires
        forall|i: int| 1 <= i < x.len() ==> x[i-1] < #[trigger] x[i],
        forall|i: int, j: int| 0 <= i < j < x.len() ==> #[trigger] x[i] < #[trigger] x[j],
    ensures
        !found ==> forall|i: int, j: int| 
            0 <= i < r.len() && 0 <= j < x.len() ==> #[trigger] r[i] != #[trigger] x[j],
        found ==> exists|i: int, j: int|
            0 <= i < r.len() && 0 <= j < x.len() && #[trigger] r[i] == #[trigger] x[j],
{
    let mut i: usize = 0;
    while i < r.len()
        invariant
            0 <= i <= r.len(),
            forall|k: int| 0 <= k < i ==> forall|j: int| 0 <= j < x.len() ==> #[trigger] r[k] != #[trigger] x[j],
    {
        let pos = binary_search(x, r[i]);
        if pos < x.len() && x[pos] == r[i] {
            return true;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

fn main() {
}

}