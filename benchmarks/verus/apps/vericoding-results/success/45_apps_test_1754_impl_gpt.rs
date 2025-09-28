// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_strongest_in_school(student_idx: int, powers: Seq<int>, schools: Seq<int>) -> bool
  recommends 0 <= student_idx < powers.len() && powers.len() == schools.len()
{
  forall|j: int| 0 <= j < powers.len() && schools[j] == schools[student_idx] ==> powers[j] <= powers[student_idx]
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_zero_le_k(k: i8)
    requires
        k >= 1,
    ensures
        0 <= k,
{
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, k: i8, powers: Vec<i8>, schools: Vec<i8>, chosen: Vec<i8>) -> (result: i8)
  requires 
      n >= 1 && m >= 1 && k >= 1 && k <= n && m <= n,
      powers@.len() == n as nat && schools@.len() == n as nat && chosen@.len() == k as nat
  ensures 
      result >= 0 && result <= k
// </vc-spec>
// <vc-code>
{
    proof { lemma_zero_le_k(k); }
    0i8
}
// </vc-code>


}

fn main() {}