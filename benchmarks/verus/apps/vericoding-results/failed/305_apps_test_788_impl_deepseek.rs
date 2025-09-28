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

proof fn digit_sum_proof(s: Seq<char>, start: int, end: int)
    requires
        0 <= start <= end <= s.len(),
        forall|i: int| start <= i < end ==> #[trigger] s[i] >= '0' && #[trigger] s[i] <= '9'
    ensures
        digit_sum(s, start, end) >= 0,
        digit_sum(s, start, end) <= 9 * (end - start)
{
    if start < end {
        digit_sum_proof(s, start + 1, end);
    }
}

proof fn zero_count_proof(s: Seq<char>, start: int, end: int)
    requires
        0 <= start <= end <= s.len()
    ensures
        0 <= zero_count(s, start, end) <= end - start
{
    if start < end {
        zero_count_proof(s, start + 1, end);
    }
}

proof fn result_bound_proof(s: Seq<char>)
    requires
        valid_input(s),
    ensures
        digit_sum(s, 1, 7) + 9 * zero_count(s, 1, 7) + 1 >= 1,
        digit_sum(s, 1, 7) + 9 * zero_count(s, 1, 7) + 1 <= 55
{
    digit_sum_proof(s, 1, 7);
    zero_count_proof(s, 1, 7);
    assert(zero_count(s, 1, 7) <= 6);
    assert(digit_sum(s, 1, 7) <= 54);
}

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires valid_input(s@)
    ensures result as int == digit_sum(s@, 1, 7) + 9 * zero_count(s@, 1, 7) + 1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed syntax error by removing incorrect requires */
    proof {
        result_bound_proof(s@);
    }
    
    let d1 = (s[1] as i8 - '0' as i8);
    let d2 = (s[2] as i8 - '0' as i8);
    let d3 = (s[3] as i8 - '0' as i8);
    let d4 = (s[4] as i8 - '0' as i8);
    let d5 = (s[5] as i8 - '0' as i8);
    let d6 = (s[6] as i8 - '0' as i8);
    
    let mut zeros = 0i8;
    if s[1] == '0' { zeros += 1; }
    if s[2] == '0' { zeros += 1; }
    if s[3] == '0' { zeros += 1; }
    if s[4] == '0' { zeros += 1; }
    if s[5] == '0' { zeros += 1; }
    if s[6] == '0' { zeros += 1; }
    
    let sum = d1 + d2 + d3 + d4 + d5 + d6;
    let result = sum + 9 * zeros + 1;
    
    proof {
        assert(result as int == digit_sum(s@, 1, 7) + 9 * zero_count(s@, 1, 7) + 1);
    }
    
    result
}
// </vc-code>


}

fn main() {}