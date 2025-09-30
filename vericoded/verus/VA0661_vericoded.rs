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
/* helper modified by LLM (iteration 2): prove nonnegativity and upper bound of max_scc_groups */
proof fn lemma_max_scc_groups_bounded_by_m(n: int, m: int)
    requires
        valid_input(n, m),
    ensures
        0 <= max_scc_groups(n, m),
        max_scc_groups(n, m) <= m,
{
    reveal(max_scc_groups);
    if valid_input(n, m) {
        let d = if n < m / 2 { n } else { m / 2 };
        assert(0 <= d);
        if n < m / 2 {
            assert(d == n);
            assert(d <= m / 2);
        } else {
            assert(d == m / 2);
            assert(d <= m / 2);
        }
        let r = m - d * 2;
        assert(2 * d <= 2 * (m / 2));
        assert(2 * (m / 2) <= m);
        assert(r >= 0);
        let a = r / 4;
        assert(a >= 0);
        let t = d + a;
        assert(t >= 0);
        assert(r <= m);
        assert(a <= m / 4);
        assert(d <= m / 2);
        assert(m / 4 <= m / 2);
        assert(d + a <= (m / 2) + (m / 4));
        assert((m / 2) + (m / 4) <= (m / 2) + (m / 2));
        assert((m / 2) + (m / 2) <= m);
        assert(t <= m);
        assert(t == max_scc_groups(n, m));
    } else {
        assert(max_scc_groups(n, m) == 0);
    }
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
    /* code modified by LLM (iteration 2): compute using i32 to avoid runtime use of spec ints; prove equality and bounds via ghost ints */
    let n32: i32 = n as i32;
    let m32: i32 = m as i32;

    let direct_groups: i32 = if n32 < m32 / 2 { n32 } else { m32 / 2 };

    proof {
        let ghost ni: int = n as int;
        let ghost mi: int = m as int;
        assert(0 <= ni && 0 <= mi);
        assert(n32 as int == ni);
        assert(m32 as int == mi);
        if n32 < m32 / 2 {
            assert(direct_groups == n32);
            assert(direct_groups <= m32 / 2);
        } else {
            assert(direct_groups == m32 / 2);
            assert(direct_groups <= m32 / 2);
        }
        assert(0 <= direct_groups);
        assert(m <= 127);
        assert(m32 <= 127);
        assert(m32 / 2 <= 63);
        assert(direct_groups <= 63);
    }

    let remaining_c_pieces: i32 = m32 - direct_groups * 2;

    proof {
        assert(2 * direct_groups <= 2 * (m32 / 2));
        assert(2 * (m32 / 2) <= m32);
        assert(remaining_c_pieces >= 0);
    }

    let additional_groups: i32 = remaining_c_pieces / 4;
    let total32: i32 = direct_groups + additional_groups;

    proof {
        let ghost ni: int = n as int;
        let ghost mi: int = m as int;
        let ghost dg: int = if ni < mi / 2 { ni } else { mi / 2 };
        let ghost rem: int = mi - dg * 2;
        let ghost add: int = rem / 4;

        assert(direct_groups as int == dg);
        assert(remaining_c_pieces as int == rem);
        assert(additional_groups as int == add);
        assert(total32 as int == dg + add);
        assert(max_scc_groups(ni, mi) == dg + add);

        lemma_max_scc_groups_bounded_by_m(ni, mi);
        assert(0 <= max_scc_groups(ni, mi));
        assert(mi <= 127);
        assert(total32 as int == max_scc_groups(ni, mi));
        assert(0 <= total32 as int);
        assert(total32 as int <= 127);
    }

    let result: i8;
    proof { assert(0 <= total32 as int && total32 as int <= 127); }
    result = total32 as i8;

    proof {
        let ghost ni: int = n as int;
        let ghost mi: int = m as int;
        assert(result as int == total32 as int);
        assert(result as int == max_scc_groups(ni, mi));
    }
    result
}
// </vc-code>


}

fn main() {}