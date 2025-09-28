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
/* helper modified by LLM (iteration 2): convert char digit to mathematical int value */
spec fn char_digit(c: char) -> int
    requires c >= '0' && c <= '9',
    ensures char_digit(c) == c as int - '0' as int
{
    c as int - '0' as int
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i8)
    requires valid_input(s@)
    ensures result as int == digit_sum(s@, 1, 7) + 9 * zero_count(s@, 1, 7) + 1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): compute total with i8 accumulator and prove correspondence with spec functions */
    let mut i: int = 1;
    let mut acc: i8 = 1i8;
    while i < 7
        invariant
            1 <= i <= 7,
            acc as int == digit_sum(s@, 1, i) + 9 * zero_count(s@, 1, i) + 1,
        decreases 7 - i
    {
        let ch: char = s[i as usize];
        let digit: i8 = ((ch as u32) - ('0' as u32)) as i8;
        let add_zero: i8 = if ch == '0' { 9i8 } else { 0i8 };
        let old_i = i;
        let new_acc = acc + digit + add_zero;
        i = i + 1;
        acc = new_acc;
        proof {
            assert(s@[old_i] == ch);
            assert(char_digit(s@[old_i]) == s@[old_i] as int - '0' as int);
            assert(digit as int == char_digit(s@[old_i]));
            assert(digit_sum(s@, 1, old_i + 1) == digit_sum(s@, 1, old_i) + char_digit(s@[old_i]));
            assert(zero_count(s@, 1, old_i + 1) == zero_count(s@, 1, old_i) + (if ch == '0' { 1 } else { 0 }));
            assert(acc as int == digit_sum(s@, 1, old_i + 1) + 9 * zero_count(s@, 1, old_i + 1) + 1);
        }
    }
    acc
}
// </vc-code>


}

fn main() {}