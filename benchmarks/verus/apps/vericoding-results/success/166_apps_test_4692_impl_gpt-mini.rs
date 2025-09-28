// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(m: int) -> bool {
    1 <= m <= 23
}

spec fn hours_until_new_year(m: int) -> int
    recommends valid_input(m)
{
    48 - m
}

spec fn valid_output(m: int, result: int) -> bool
    recommends valid_input(m)
{
    result == hours_until_new_year(m) && 25 <= result <= 47
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove hours_until_new_year is between 25 and 47 */
proof fn hours_bounds(m: int)
    requires valid_input(m),
    ensures 25 <= hours_until_new_year(m) <= 47,
{
    assert(hours_until_new_year(m) == 48 - m);
    assert(25 <= 48 - m && 48 - m <= 47);
}

// </vc-helpers>

// <vc-spec>
fn solve(m: i8) -> (result: i8)
    requires valid_input(m as int)
    ensures valid_output(m as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute result in i8 and prove it matches spec hours_until_new_year */
    let result: i8 = 48 - m;
    proof {
        let m_int: int = m as int;
        let r_int: int = hours_until_new_year(m_int);
        hours_bounds(m_int);
        assert(r_int == 48 - m_int);
        assert((result as int) == 48 - m_int);
        assert((result as int) == r_int);
        assert(25 <= r_int && r_int <= 47);
        assert(-128 <= r_int && r_int <= 127);
    }
    result
}

// </vc-code>


}

fn main() {}