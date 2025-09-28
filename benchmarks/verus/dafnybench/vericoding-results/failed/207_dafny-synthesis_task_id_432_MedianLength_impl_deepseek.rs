use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_div_plus(a: int, b: int)
    requires
        a > 0 && b > 0,
    ensures
        (a + b) / 2 * 2 <= a + b,
        (a + b) / 2 * 2 + 2 > a + b,
{
    assert((a + b) / 2 * 2 <= a + b);
    assert((a + b) / 2 * 2 + 2 > a + b);
}
// </vc-helpers>

// <vc-spec>
fn median_length(a: int, b: int) -> (median: int)
    requires a > 0 && b > 0
    ensures median == (a + b) / 2
// </vc-spec>
// <vc-code>
{
  proof {
    lemma_div_plus(a, b);
  }
  let median: int = (a + b) / 2;
  median
}
// </vc-code>

fn main() {}

}