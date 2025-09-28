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

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires valid_input(s@)
    ensures result as int == digit_sum(s@, 1, 7) + 9 * zero_count(s@, 1, 7) + 1
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error: cannot index into a value of type `vstd::seq::Seq<char>` by modifying `s_seq[i]` to `s_seq[i as int]`, and also added `i` to decreases clause. */
{
    let s_seq = s@;

    let mut sum_digits: i8 = 0;
    let mut count_zeros: i8 = 0;
    let mut i: usize = 1;

    while i < 7
        invariant
            1 <= i && i <= 7,
            sum_digits as int == digit_sum(s_seq, 1, i as int),
            count_zeros as int == zero_count(s_seq, 1, i as int),
        decreases 7 - i
    {
        let digit_val = (s_seq[i as int] as char) as i8 - ('0' as char) as i8;
        sum_digits = sum_digits + digit_val;
        if s_seq[i as int] == '0' {
            count_zeros = count_zeros + 1;
        }
        i = i + 1;
    }

    let result_int = sum_digits + 9 * count_zeros + 1;
    (result_int as i8)
}
// </vc-code>


}

fn main() {}