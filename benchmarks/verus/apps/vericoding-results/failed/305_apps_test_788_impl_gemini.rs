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
lemma fn lemma_digit_sum_bounds(s: Seq<char>, start: int, end: int)
    requires
        0 <= start <= end <= s.len(),
        forall|i: int| start <= i < end ==> #[trigger] s[i] >= '0' && s[i] <= '9',
    ensures
        0 <= digit_sum(s, start, end) <= 9 * (end - start),
    decreases end - start
{
    if start < end {
        lemma_digit_sum_bounds(s, start + 1, end);
        let d = s[start] as int - '0' as int;
        assert(0 <= d <= 9);
    }
}

lemma fn lemma_zero_count_bounds(s: Seq<char>, start: int, end: int)
    requires
        0 <= start <= end <= s.len(),
    ensures
        0 <= zero_count(s, start, end) <= end - start,
    decreases end - start
{
    if start < end {
        lemma_zero_count_bounds(s, start + 1, end);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires valid_input(s@)
    ensures result as int == digit_sum(s@, 1, 7) + 9 * zero_count(s@, 1, 7) + 1
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 1;
    let mut current_sum: int = 0;
    let mut num_zeros: int = 0;
    while i < 7
        invariant
            1 <= i <= 7,
            valid_input(s@),
            current_sum == digit_sum(s@, 1, i as int),
            num_zeros == zero_count(s@, 1, i as int),
        decreases 7 - i
    {
        let c = s[i];
        let digit = c as int - '0' as int;
        current_sum = current_sum + digit;
        if c == '0' {
            num_zeros = num_zeros + 1;
        }
        i = i + 1;
    }

    let result_int = current_sum + 9 * num_zeros + 1;

    proof {
        lemma_digit_sum_bounds(s@, 1, 7);
        lemma_zero_count_bounds(s@, 1, 7);
    }

    let result = result_int as i8;
    result
}
// </vc-code>


}

fn main() {}