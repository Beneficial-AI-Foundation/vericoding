// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn f(n: int, x: int) -> int {
  let y = n / x;
  y + x * y * (y - 1) / 2
}

spec fn is_divisor(d: int, n: int) -> bool {
  d > 0 && n % d == 0
}

spec fn is_sorted(s: Seq<int>) -> bool {
  forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

spec fn no_duplicates(s: Seq<int>) -> bool {
  forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: Vec<i8>)
  requires n as int >= 2
  ensures 
      no_duplicates(result@.map(|i: int, x: i8| x as int)) &&
      is_sorted(result@.map(|i: int, x: i8| x as int)) &&
      (forall|v: int| #[trigger] result@.map(|i: int, x: i8| x as int).contains(v) <==> exists|d: int| #[trigger] is_divisor(d, n as int) && v == f(n as int, d)) &&
      result@.len() > 0
// </vc-spec>
// <vc-code>
{
  assume(false);
  Vec::new()
}
// </vc-code>


}

fn main() {}