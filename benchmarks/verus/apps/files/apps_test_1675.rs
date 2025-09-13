// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, teams: Seq<(int, int)>) -> bool {
  n >= 2 && teams.len() == n &&
  (forall|i: int| 0 <= i < n ==> teams[i].0 != teams[i].1) &&
  (forall|i: int| 0 <= i < n ==> 
    Set::new(|j: int| 0 <= j < n && teams[j].0 == teams[i].1).len() <= n - 1)
}

spec fn valid_output(n: int, teams: Seq<(int, int)>, result: Seq<(int, int)>) -> bool {
  teams.len() == n ==>
  result.len() == n &&
  (forall|i: int| 0 <= i < n ==> result[i].0 + result[i].1 == 2 * (n - 1)) &&
  (forall|i: int| 0 <= i < n ==> result[i].0 >= n - 1) &&
  (forall|i: int| 0 <= i < n ==> result[i].1 >= 0) &&
  (forall|i: int| 0 <= i < n ==> {
    let home_count = Set::new(|j: int| 0 <= j < n && teams[j].0 == teams[i].1).len();
    result[i].0 == (n - 1) + home_count &&
    result[i].1 == (n - 1) - home_count
  })
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, teams: Seq<(int, int)>) -> (result: Seq<(int, int)>)
  requires valid_input(n, teams)
  ensures valid_output(n, teams, result)
// </vc-spec>
// <vc-code>
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}