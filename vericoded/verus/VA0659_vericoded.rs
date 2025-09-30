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
/* helper modified by LLM (iteration 2): range lemma for hours_until_new_year */
proof fn lemma_hours_in_range(m: int)
    requires
        valid_input(m),
    ensures
        25 <= hours_until_new_year(m),
        hours_until_new_year(m) <= 47,
{
    reveal(hours_until_new_year);
    assert(1 <= m);
    assert(m <= 23);
    assert(48 - m >= 48 - 23);
    assert(48 - m <= 48 - 1);
    assert(48 - 23 == 25);
    assert(48 - 1 == 47);
}

// </vc-helpers>

// <vc-spec>
fn solve(m: i8) -> (result: i8)
    requires valid_input(m as int)
    ensures valid_output(m as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): compute result via a counted loop with invariants, avoiding exec int variables */
    let mut curr: i8 = m;
    let mut result: i8 = 0i8;

    while curr < 48i8
        invariant
            valid_input(m as int),
            1 <= curr as int,
            curr as int <= 48,
            0 <= result as int,
            result as int <= 47,
            result as int == curr as int - m as int,
        decreases 48 - curr as int
    {
        proof {
            if curr < 48i8 {
                assert(curr as int <= 47);
                assert(m as int >= 1);
                assert(result as int == curr as int - m as int);
                assert(result as int <= 46);
            }
        }
        result = result + 1i8;
        curr = curr + 1i8;
    }

    proof {
        reveal(hours_until_new_year);
        if curr < 48i8 { assert(false); } else { assert(curr as int >= 48); }
        assert(curr as int <= 48);
        assert(curr as int == 48);
        assert(result as int == 48 - m as int);
        lemma_hours_in_range(m as int);
        assert(result as int == hours_until_new_year(m as int));
    }

    result
}
// </vc-code>


}

fn main() {}