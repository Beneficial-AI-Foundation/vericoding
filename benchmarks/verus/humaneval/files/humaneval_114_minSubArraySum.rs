// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum(a: Seq<int>, s: int, t: int) -> int
  decreases t - s
{
  if 0 <= s <= t <= a.len() {
    if s == t {
      0
    } else {
      sum(a, s, t - 1) + a[t - 1]
    }
  } else {
    0
  }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn min_sub_array_sum(a: Vec<int>) -> (s: int)
  ensures 
    forall|p: int, q: int| 0 <= p <= q <= a@.len() ==> sum(a@, p, q) >= s as int,
    exists|k: int, m: int| 0 <= k <= m <= a@.len() && s as int == sum(a@, k, m)
// </vc-spec>
// <vc-code>
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}