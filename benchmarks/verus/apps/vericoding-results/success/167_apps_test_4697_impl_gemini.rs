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
/* helper modified by LLM (iteration 3): no functional changes, updating comment */
fn min(a: i8, b: i8) -> (res: i8)
    requires a >= 0 && b >= 0,
    ensures
        res >= 0,
        res <= a,
        res <= b,
        res as int == (if (a as int) < (b as int) { a as int } else { b as int }),
{
    if a < b { a } else { b }
}
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
    /* code modified by LLM (iteration 3): fix compilation error by removing incorrect lemma call */
    let direct_groups = min(n, m / 2);
    let remaining_c_pieces = m - direct_groups * 2;
    let additional_groups = remaining_c_pieces / 4;
    let result = direct_groups + additional_groups;

    proof {
        let n_int = n as int;
        let m_int = m as int;

        let spec_direct_groups = if n_int < m_int / 2 { n_int } else { m_int / 2 };
        assert(direct_groups as int == spec_direct_groups);

        let spec_remaining_c_pieces = m_int - spec_direct_groups * 2;
        assert(remaining_c_pieces as int == spec_remaining_c_pieces);

        if n_int >= m_int / 2 {
            // spec_remaining_c_pieces is m_int - (m_int / 2) * 2, which is m_int % 2.
            // The required lemma, `lemma_div_is_div_mod`, is broadcast.
            assert(spec_remaining_c_pieces == m_int % 2);
        }
        assert(remaining_c_pieces >= 0);

        let spec_additional_groups = spec_remaining_c_pieces / 4;
        assert(additional_groups as int == spec_additional_groups);

        assert(result as int == max_scc_groups(n_int, m_int));
    }

    result
}
// </vc-code>


}

fn main() {}