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
spec fn compute_digit_sum(s: Seq<char>, start: int, end: int) -> int
    requires
        0 <= start <= end <= s.len(),
        forall|i: int| 0 <= i < s.len() ==> s[i] >= '0' && s[i] <= '9',
    decreases end - start
{
    if start >= end {
        0
    } else {
        (s[start] as int - '0' as int) + compute_digit_sum(s, start + 1, end)
    }
}

spec fn compute_zero_count(s: Seq<char>, start: int, end: int) -> int
    requires
        0 <= start <= end <= s.len(),
        forall|i: int| 0 <= i < s.len() ==> s[i] >= '0' && s[i] <= '9',
    decreases end - start
{
    if start >= end {
        0
    } else {
        (if s[start] == '0' { 1int } else { 0int }) + compute_zero_count(s, start + 1, end)
    }
}

proof fn lemma_digit_sum_eq(s: Seq<char>, start: int, end: int)
    requires
        0 <= start <= end <= s.len(),
        forall|i: int| 1 <= i < s.len() ==> s[i] >= '0' && s[i] <= '9',
    ensures digit_sum(s, start, end) == compute_digit_sum(s, start, end)
    decreases end - start
{
    if start >= end {
    } else {
        lemma_digit_sum_eq(s, start + 1, end);
    }
}

proof fn lemma_zero_count_eq(s: Seq<char>, start: int, end: int)
    requires
        0 <= start <= end <= s.len(),
        forall|i: int| 1 <= i < s.len() ==> s[i] >= '0' && s[i] <= '9',
    ensures zero_count(s, start, end) == compute_zero_count(s, start, end)
    decreases end - start
{
    if start >= end {
    } else {
        lemma_zero_count_eq(s, start + 1, end);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires valid_input(s@)
    ensures result as int == digit_sum(s@, 1, 7) + 9 * zero_count(s@, 1, 7) + 1
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): fixed compilation errors: wrapped lemma calls in proof block, removed as int from literals. */
{
    let s_seq = s@;
    proof {
        lemma_digit_sum_eq(s_seq, 1, 7);
        lemma_zero_count_eq(s_seq, 1, 7);
    }
    let mut sum: i32 = 0;
    let mut zeros: i32 = 0;
    let mut i: usize = 1;
    while i < 7
        invariant
            1 <= i as int <= 7,
            sum as int == compute_digit_sum(s@, 1, i as int),
            zeros as int == compute_zero_count(s@, 1, i as int),
        decreases 7 - i
    {
        let d = (s[i] as u32) - ('0' as u32);
        sum += d as i32;
        if s[i] == '0' {
            zeros += 1;
        }
        i += 1;
    }
    let result = sum + 9 * zeros + 1;
    assert(result as int == digit_sum(s@, 1, 7) + 9 * zero_count(s@, 1, 7) + 1);
    result as i8
}
// </vc-code>


}

fn main() {}