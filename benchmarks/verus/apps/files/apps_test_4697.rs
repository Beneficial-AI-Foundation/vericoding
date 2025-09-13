// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, m: int) -> bool {
    n >= 0 && m >= 0
}

spec fn max_scc_groups(n: int, m: int) -> int {
    if valid_input(n, m) {
        let direct_groups = if n < m / 2 { n } else { m / 2 };
        let remaining_c_pieces = m - direct_groups * 2;
        let additional_groups = remaining_c_pieces / 4;
        direct_groups + additional_groups
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, m: int) -> (result: int)
  requires valid_input(n, m)
  ensures 
      result >= 0,
      result == max_scc_groups(n, m),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}