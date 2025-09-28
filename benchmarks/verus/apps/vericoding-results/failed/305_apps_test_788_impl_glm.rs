// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() == 7 && s[0] == 'A' && forall|i: int| 1 <= i < 7 ==> #[trigger] s[i] >= '0' && #[trigger] s[i] <= '9'
}

spec fn digit_sum(s: Seq<char>, start: int, end: int) -> int
    decreases end - start when 0 <= start <= end <= s.len()
{
    if start >= end {
        0
    } else {
        (s[start] as int - '0' as int) + digit_sum(s, start + 1, end)
    }
}

spec fn zero_count(s: Seq<char>, start: int, end: int) -> int
    decreases end - start when 0 <= start <= end <= s.len()
{
    if start >= end {
        0
    } else {
        (if s[start] == '0' { 1nat } else { 0nat }) as int + zero_count(s, start + 1, end)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fixed lemma declaration by adding 'proof' keyword */
proof lemma digit_sum_unroll(s: Seq<char>)
    requires valid_input(s)
    ensures digit_sum(s, 1, 7) == (s[1] as int - '0' as int) + 
                                         (s[2] as int - '0' as int) +
                                         (s[3] as int - '0' as int) +
                                         (s[4] as int - '0' as int) +
                                         (s[5] as int - '0' as int) +
                                         (s[6] as int - '0' as int)
{
    assert(digit_sum(s, 1, 7) == (s[1] as int - '0' as int) + digit_sum(s, 2, 7));
    assert(digit_sum(s, 2, 7) == (s[2] as int - '0' as int) + digit_sum(s, 3, 7));
    assert(digit_sum(s, 3, 7) == (s[3] as int - '0' as int) + digit_sum(s, 4, 7));
    assert(digit_sum(s, 4, 7) == (s[4] as int - '0' as int) + digit_sum(s, 5, 7));
    assert(digit_sum(s, 5, 7) == (s[5] as int - '0' as int) + digit_sum(s, 6, 7));
    assert(digit_sum(s, 6, 7) == (s[6] as int - '0' as int) + digit_sum(s, 7, 7));
    assert(digit_sum(s, 7, 7) == 0);
}

/* helper modified by LLM (iteration 4): fixed lemma declaration by adding 'proof' keyword */
proof lemma zero_count_unroll(s: Seq<char>)
    requires valid_input(s)
    ensures zero_count(s, 1, 7) == (if s[1]=='0' { 1 } else { 0 }) +
                                          (if s[2]=='0' { 1 } else { 0 }) +
                                          (if s[3]=='0' { 1 } else { 0 }) +
                                          (if s[4]=='0' { 1 } else { 0 }) +
                                          (if s[5]=='0' { 1 } else { 0 }) +
                                          (if s[6]=='0' { 1 } else { 0 })
{
    assert(zero_count(s, 1, 7) == (if s[1]=='0' { 1 } else { 0 }) + zero_count(s, 2, 7));
    assert(zero_count(s, 2, 7) == (if s[2]=='0' { 1 } else { 0 }) + zero_count(s, 3, 7));
    assert(zero_count(s, 3, 7) == (if s[3]=='0' { 1 } else { 0 }) + zero_count(s, 4, 7));
    assert(zero_count(s, 4, 7) == (if s[4]=='0' { 1 } else { 0 }) + zero_count(s, 5, 7));
    assert(zero_count(s, 5, 7) == (if s[5]=='0' { 1 } else { 0 }) + zero_count(s, 6, 7));
    assert(zero_count(s, 6, 7) == (if s[6]=='0' { 1 } else { 0 }) + zero_count(s, 7, 7));
    assert(zero_count(s, 7, 7) == 0);
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires valid_input(s@)
    ensures result as int == digit_sum(s@, 1, 7) + 9 * zero_count(s@, 1, 7) + 1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): updated to use fixed lemmas (no logic change) */
    let d1 = (s[1] as i8 - '0' as i8);
    let d2 = (s[2] as i8 - '0' as i8);
    let d3 = (s[3] as i8 - '0' as i8);
    let d4 = (s[4] as i8 - '0' as i8);
    let d5 = (s[5] as i8 - '0' as i8);
    let d6 = (s[6] as i8 - '0' as i8);
    let total = d1 + d2 + d3 + d4 + d5 + d6;

    let z1 = if s[1]=='0' { 1i8 } else { 0i8 };
    let z2 = if s[2]=='0' { 1i8 } else { 0i8 };
    let z3 = if s[3]=='0' { 1i8 } else { 0i8 };
    let z4 = if s[4]=='0' { 1i8 } else { 0i8 };
    let z5 = if s[5]=='0' { 1i8 } else { 0i8 };
    let z6 = if s[6]=='0' { 1i8 } else { 0i8 };
    let zeros = z1 + z2 + z3 + z4 + z5 + z6;

    let result = total + 9i8 * zeros + 1i8;

    proof {
        digit_sum_unroll(s@);
        zero_count_unroll(s@);

        assert((s[1] as i8 - '0' as i8) as int == s[1] as int - '0' as int);
        assert((s[2] as i8 - '0' as i8) as int == s[2] as int - '0' as int);
        assert((s[3] as i8 - '0' as i8) as int == s[3] as int - '0' as int);
        assert((s[4] as i8 - '0' as i8) as int == s[4] as int - '0' as int);
        assert((s[5] as i8 - '0' as i8) as int == s[5] as int - '0' as int);
        assert((s[6] as i8 - '0' as i8) as int == s[6] as int - '0' as int);

        assert(total as int == (s[1] as int - '0' as int) + (s[2] as int - '0' as int) + 
                             (s[3] as int - '0' as int) + (s[4] as int - '0' as int) +
                             (s[5] as int - '0' as int) + (s[6] as int - '0' as int));
        assert(total as int == digit_sum(s@, 1, 7));

        assert((if s[1]=='0' { 1i8 } else { 0i8 }) as int == (if s[1]=='0' { 1 } else { 0 }));
        assert((if s[2]=='0' { 1i8 } else { 0i8 }) as int == (if s[2]=='0' { 1 } else { 0 }));
        assert((if s[3]=='0' { 1i8 } else { 0i8 }) as int == (if s[3]=='0' { 1 } else { 0 }));
        assert((if s[4]=='0' { 1i8 } else { 0i8 }) as int == (if s[4]=='0' { 1 } else { 0 }));
        assert((if s[5]=='0' { 1i8 } else { 0i8 }) as int == (if s[5]=='0' { 1 } else { 0 }));
        assert((if s[6]=='0' { 1i8 } else { 0i8 }) as int == (if s[6]=='0' { 1 } else { 0 }));

        assert(zeros as int == (if s[1]=='0' { 1 } else { 0 }) + (if s[2]=='0' { 1 } else { 0 }) +
                             (if s[3]=='0' { 1 } else { 0 }) + (if s[4]=='0' { 1 } else { 0 }) +
                             (if s[5]=='0' { 1 } else { 0 }) + (if s[6]=='0' { 1 } else { 0 }));
        assert(zeros as int == zero_count(s@, 1, 7));
    }

    result
}
// </vc-code>


}

fn main() {}