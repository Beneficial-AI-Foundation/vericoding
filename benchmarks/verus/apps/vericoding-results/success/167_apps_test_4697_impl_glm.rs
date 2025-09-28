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
fn solve(n: i8, m: i8) -> (result: i8)
  requires valid_input(n as int, m as int)
  ensures 
      result >= 0,
      result as int == max_scc_groups(n as int, m as int),
// </vc-spec>
// <vc-code>
{
    let direct_groups = if n < m / 2 { n } else { m / 2 };
    let remaining_c_pieces = m - direct_groups * 2;
    let additional_groups = remaining_c_pieces / 4;
    let result = direct_groups + additional_groups;

    proof {
        let spec_direct = if (n as int) < (m as int) / 2 { n as int } else { (m as int) / 2 };
        let spec_remaining = (m as int) - spec_direct * 2;
        let spec_additional = spec_remaining / 4;
        let spec_result = spec_direct + spec_additional;
        assert(direct_groups as int == spec_direct);
        assert(remaining_c_pieces as int == spec_remaining);
        assert(additional_groups as int == spec_additional);
        assert(result as int == spec_result);
        assert(spec_result == max_scc_groups(n as int, m as int));
    }

    result
}
// </vc-code>


}

fn main() {}