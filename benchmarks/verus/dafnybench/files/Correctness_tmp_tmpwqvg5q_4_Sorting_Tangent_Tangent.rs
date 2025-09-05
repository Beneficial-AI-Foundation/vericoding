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
// </vc-helpers>

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
// <vc-code>
{
    assume(false);
    false
}
// </vc-code>


fn main() {
}

}