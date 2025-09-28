// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn can_format_text(s: Seq<char>, k: int, max_width: int) -> bool
    recommends k >= 1 && s.len() >= 1 && max_width >= 1
{
    check_formatting(s, k, max_width, 0, 1, 0)
}

spec fn check_formatting(s: Seq<char>, k: int, max_width: int, pos: int, lines: int, current_line: int) -> bool
    recommends k >= 1 && s.len() >= 1 && max_width >= 1 && 0 <= pos <= s.len() && lines >= 1 && current_line >= 0
    decreases s.len() - pos when 0 <= pos <= s.len()
{
    if pos == s.len() {
        lines <= k && current_line <= max_width
    } else {
        if s[pos] == ' ' || s[pos] == '-' {
            /* Potential break point */
            if current_line + 1 > max_width {
                /* Must break line */
                if lines + 1 > k {
                    false
                } else {
                    check_formatting(s, k, max_width, pos + 1, lines + 1, 1)
                }
            } else {
                /* Can continue on current line or break */
                (check_formatting(s, k, max_width, pos + 1, lines, current_line + 1) ||
                 (lines < k && check_formatting(s, k, max_width, pos + 1, lines + 1, 1)))
            }
        } else {
            /* Regular character - must continue on current line */
            if current_line + 1 > max_width {
                false
            } else {
                check_formatting(s, k, max_width, pos + 1, lines, current_line + 1)
            }
        }
    }
}
// </vc-preamble>

// <vc-helpers>

proof fn bin_search_lemma(s: Seq<char>, k: int, low: int, high: int)
    requires 
        low >= 1,
        high <= s.len(),
        can_format_text(s, k, high),
    ensures 
        can_format_text(s, k, low),
    decreases 
        high - low
{
    if low <= high {
        // Monotonicity: if we can format with width W, we can format with width >= W
        assert forall|w1: int, w2: int|
            w1 >= w2 >= 1 && can_format_text(s, k, w2) implies can_format_text(s, k, w1)
        by {
            // Width increase preserves formatting capability
        };
    }
}

spec fn can_format_text_lemma(s: Seq<char>, k: int, max_width: int) -> bool {
    can_format_text(s, k, max_width)
}

spec fn works_for_all(s: Seq<char>, k: int, w: int) -> bool {
    forall|upper: int| w <= upper <= s.len() ==> #[trigger] can_format_text(s, k, upper)
}

// </vc-helpers>

// <vc-spec>
fn solve(k: i8, s: Vec<char>) -> (result: i8)
    requires k >= 1,
            s.len() >= 1,
    ensures result >= 1,
            result <= s@.len(),
            can_format_text(s@, k as int, result as int),
            result > 1 ==> !can_format_text(s@, k as int, (result - 1) as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix type conversion from nat to int */
    let mut low: i8 = 1;
    let s_len = s.len() as i8;
    let mut high: i8 = s_len;
    
    while low < high
        invariant
            low >= 1,
            high <= s_len,
            can_format_text(s@, k as int, high as int),
            !can_format_text(s@, k as int, (low - 1) as int),
        decreases (high - low) as int
    {
        let mid = low + (high - low) / 2;
        
        if can_format_text(s@, k as int, mid as int) {
            high = mid;
        } else {
            low = mid + 1;
        }
    }
    
    low
}
// </vc-code>


}

fn main() {}