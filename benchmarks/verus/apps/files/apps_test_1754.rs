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
    powers.len() == n && schools.len() == n && chosen.len() == k,
    forall|i: int| 0 <= i < n ==> 1 <= schools[i] <= m,
    forall|i: int| 0 <= i < k ==> 1 <= chosen[i] <= n,
    forall|i: int, j: int| 0 <= i < k && 0 <= j < k && i != j ==> chosen[i] != chosen[j],
    forall|i: int, j: int| 0 <= i < n && 0 <= j < n && i != j ==> powers[i] != powers[j],
    forall|s: int| 1 <= s <= m ==> exists|i: int| 0 <= i < n && schools[i] == s,
    forall|i: int| 0 <= i < n ==> 1 <= powers[i] <= n
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