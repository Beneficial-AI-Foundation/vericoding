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
/* helper modified by LLM (iteration 5): Added lemmas to properly maintain sum invariant */
proof fn lemma_digit_sum_step(s: Seq<char>, start: int, end: int)
    requires
        0 <= start < end <= s.len(),
        s[start] >= '0' && s[start] <= '9',
    ensures
        digit_sum(s, start, end) == (s[start] as int - '0' as int) + digit_sum(s, start + 1, end),
    decreases end - start,
{
    // Follows directly from definition
}

proof fn lemma_zero_count_step(s: Seq<char>, start: int, end: int)
    requires
        0 <= start < end <= s.len(),
    ensures
        zero_count(s, start, end) == (if s[start] == '0' { 1int } else { 0int }) + zero_count(s, start + 1, end),
    decreases end - start,
{
    // Follows directly from definition
}

proof fn lemma_digit_sum_bounds(s: Seq<char>, start: int, end: int)
    requires
        0 <= start <= end <= s.len(),
        forall|i: int| start <= i < end ==> s[i] >= '0' && s[i] <= '9',
    ensures
        0 <= digit_sum(s, start, end) <= 9 * (end - start),
    decreases end - start,
{
    if start >= end {
        assert(digit_sum(s, start, end) == 0);
    } else {
        assert(s[start] >= '0' && s[start] <= '9');
        assert(0 <= s[start] as int - '0' as int <= 9);
        lemma_digit_sum_bounds(s, start + 1, end);
    }
}

proof fn lemma_zero_count_bounds(s: Seq<char>, start: int, end: int)
    requires
        0 <= start <= end <= s.len(),
    ensures
        0 <= zero_count(s, start, end) <= end - start,
    decreases end - start,
{
    if start >= end {
        assert(zero_count(s, start, end) == 0);
    } else {
        lemma_zero_count_bounds(s, start + 1, end);
    }
}

proof fn lemma_sum_update(s: Seq<char>, i: int)
    requires
        1 <= i < 7,
        s.len() == 7,
        s[i] >= '0' && s[i] <= '9',
    ensures
        digit_sum(s, 1, i + 1) == digit_sum(s, 1, i) + (s[i] as int - '0' as int),
        zero_count(s, 1, i + 1) == zero_count(s, 1, i) + (if s[i] == '0' { 1int } else { 0int }),
{
    lemma_digit_sum_step(s, i, i + 1);
    assert(digit_sum(s, i, i + 1) == s[i] as int - '0' as int);
    lemma_zero_count_step(s, i, i + 1);
    assert(zero_count(s, i, i + 1) == if s[i] == '0' { 1int } else { 0int });
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires valid_input(s@)
    ensures result as int == digit_sum(s@, 1, 7) + 9 * zero_count(s@, 1, 7) + 1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed sum update to properly maintain invariant */
    let mut sum: i32 = 0;
    let mut i: usize = 1;
    
    proof {
        lemma_digit_sum_bounds(s@, 1, 7);
        lemma_zero_count_bounds(s@, 1, 7);
        assert(0 <= digit_sum(s@, 1, 7) <= 54);
        assert(0 <= zero_count(s@, 1, 7) <= 6);
        assert(0 <= digit_sum(s@, 1, 7) + 9 * zero_count(s@, 1, 7) <= 54 + 54);
    }
    
    while i < 7
        invariant
            1 <= i <= 7,
            s@.len() == 7,
            valid_input(s@),
            sum == digit_sum(s@, 1, i as int) + 9 * zero_count(s@, 1, i as int),
            0 <= sum <= 108,
        decreases 7 - i,
    {
        assert(s@[i as int] >= '0' && s@[i as int] <= '9');
        let c = s[i];
        assert(c >= '0' && c <= '9');
        let digit = (c as i32) - ('0' as i32);
        assert(0 <= digit <= 9);
        
        let old_sum = sum;
        sum = sum + digit;
        if c == '0' {
            sum = sum + 9;
        }
        
        proof {
            lemma_sum_update(s@, i as int);
            assert(digit_sum(s@, 1, (i + 1) as int) == digit_sum(s@, 1, i as int) + digit);
            assert(zero_count(s@, 1, (i + 1) as int) == zero_count(s@, 1, i as int) + (if c == '0' { 1int } else { 0int }));
            
            if c == '0' {
                assert(sum == old_sum + digit + 9);
                assert(sum == digit_sum(s@, 1, i as int) + 9 * zero_count(s@, 1, i as int) + digit + 9);
                assert(sum == digit_sum(s@, 1, (i + 1) as int) + 9 * (zero_count(s@, 1, i as int) + 1));
                assert(sum == digit_sum(s@, 1, (i + 1) as int) + 9 * zero_count(s@, 1, (i + 1) as int));
            } else {
                assert(sum == old_sum + digit);
                assert(sum == digit_sum(s@, 1, i as int) + 9 * zero_count(s@, 1, i as int) + digit);
                assert(sum == digit_sum(s@, 1, (i + 1) as int) + 9 * zero_count(s@, 1, (i + 1) as int));
            }
            
            lemma_digit_sum_bounds(s@, 1, (i + 1) as int);
            lemma_zero_count_bounds(s@, 1, (i + 1) as int);
            assert(0 <= digit_sum(s@, 1, (i + 1) as int) <= 9 * ((i + 1) as int - 1));
            assert(0 <= zero_count(s@, 1, (i + 1) as int) <= (i + 1) as int - 1);
            assert(0 <= sum && sum <= 108);
        }
        
        i = i + 1;
    }
    
    assert(sum == digit_sum(s@, 1, 7) + 9 * zero_count(s@, 1, 7));
    let result = (sum + 1) as i8;
    assert(result as int == digit_sum(s@, 1, 7) + 9 * zero_count(s@, 1, 7) + 1);
    result
}
// </vc-code>


}

fn main() {}