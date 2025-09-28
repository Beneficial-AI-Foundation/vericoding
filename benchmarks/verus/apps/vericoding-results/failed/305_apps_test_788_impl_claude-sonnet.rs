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
/* helper modified by LLM (iteration 5): fixed integer literal types */
fn lemma_digit_sum_empty(s: Seq<char>, start: int)
    requires start >= 0
    ensures digit_sum(s, start, start) == 0
{
}

fn lemma_zero_count_empty(s: Seq<char>, start: int)
    requires start >= 0
    ensures zero_count(s, start, start) == 0
{
}

fn lemma_digit_sum_step(s: Seq<char>, start: int, end: int)
    requires 0 <= start < end <= s.len(),
             s[start] >= '0' && s[start] <= '9'
    ensures digit_sum(s, start, end) == (s[start] as int - '0' as int) + digit_sum(s, start + 1, end)
{
}

fn lemma_zero_count_step(s: Seq<char>, start: int, end: int)
    requires 0 <= start < end <= s.len()
    ensures zero_count(s, start, end) == (if s[start] == '0' { 1int } else { 0int }) + zero_count(s, start + 1, end)
{
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires valid_input(s@)
    ensures result as int == digit_sum(s@, 1, 7) + 9 * zero_count(s@, 1, 7) + 1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added decreases clause */
    let mut sum = 0i8;
    let mut zeros = 0i8;
    let mut i = 1;
    
    while i < 7
        invariant
            1 <= i <= 7,
            sum as int == digit_sum(s@, 1, i as int),
            zeros as int == zero_count(s@, 1, i as int),
            valid_input(s@),
        decreases 7 - i
    {
        let digit_val = (s[i] as u8 - '0' as u8) as i8;
        sum = sum + digit_val;
        
        if s[i] == '0' {
            zeros = zeros + 1;
        }
        
        i = i + 1;
    }
    
    sum + 9 * zeros + 1
}
// </vc-code>


}

fn main() {}