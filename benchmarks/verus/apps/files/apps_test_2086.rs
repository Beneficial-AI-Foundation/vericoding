// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, a: Seq<int>, s: int, f: int) -> bool {
  n >= 2 && a.len() == n && s >= 1 && f > s && f <= n &&
  forall|i: int| 0 <= i < n ==> a[i] >= 1
}

spec fn participant_count(a: Seq<int>, s: int, f: int, n: int, start: int) -> int {
  participant_count_helper(a, s, f, n, start, 0)
}

spec fn participant_count_helper(a: Seq<int>, s: int, f: int, n: int, start: int, i: int) -> int
  decreases n - i
{
  if i >= n {
    0
  } else {
    let local_hour = (start + i - 1) % n + 1;
    let contribution = if s <= local_hour < f { a[i] } else { 0 };
    contribution + participant_count_helper(a, s, f, n, start, i + 1)
  }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, a: Seq<int>, s: int, f: int) -> (result: int)
  requires 
    valid_input(n, a, s, f),
  ensures 
    1 <= result <= n,
  ensures 
    forall|start: int| 1 <= start <= n ==> 
      participant_count(a, s, f, n, result) >= participant_count(a, s, f, n, start),
  ensures 
    forall|start: int| 1 <= start <= n && 
      participant_count(a, s, f, n, start) == participant_count(a, s, f, n, result) 
      ==> result <= start,
// </vc-spec>
// <vc-code>
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}