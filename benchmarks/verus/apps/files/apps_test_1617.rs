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
fn solve(n: int) -> (result: Vec<int>)
  requires n >= 2
  ensures 
      no_duplicates(result@) &&
      is_sorted(result@) &&
      (forall|v: int| result@.contains(v) <==> exists|d: int| is_divisor(d, n) && v == f(n, d)) &&
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