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
// </vc-helpers>

// <vc-spec>
fn solve(n: int, m: int, k: int, powers: Seq<int>, schools: Seq<int>, chosen: Seq<int>) -> (result: int)
  requires 
      n >= 1 && m >= 1 && k >= 1 && k <= n && m <= n,
      powers.len() == n && schools.len() == n && chosen.len() == k
  ensures 
      result >= 0 && result <= k
// </vc-spec>
// <vc-code>
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}