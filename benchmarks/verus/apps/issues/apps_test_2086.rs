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
fn solve(n: i8, a: Vec<i8>, s: i8, f: i8) -> (result: i8)
  requires 
    valid_input(n as int, a@.map(|i, x| x as int), s as int, f as int),
  ensures 
    1 <= result <= n &&
    (forall|start: int| #[trigger] participant_count(a@.map(|i, x| x as int), s as int, f as int, n as int, start) 
      && 1 <= start <= n as int ==> 
      participant_count(a@.map(|i, x| x as int), s as int, f as int, n as int, result as int) >= participant_count(a@.map(|i, x| x as int), s as int, f as int, n as int, start)) &&
    (forall|start: int| #[trigger] participant_count(a@.map(|i, x| x as int), s as int, f as int, n as int, start)
      && 1 <= start <= n as int && 
      participant_count(a@.map(|i, x| x as int), s as int, f as int, n as int, start) == participant_count(a@.map(|i, x| x as int), s as int, f as int, n as int, result as int) 
      ==> result as int <= start)
// </vc-spec>
// <vc-code>
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}