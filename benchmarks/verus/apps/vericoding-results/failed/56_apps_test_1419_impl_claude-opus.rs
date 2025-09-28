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
    /* code modified by LLM (iteration 5): added s.len() bound, fixed loop invariants and formatting simulation */
    
    // Ensure s.len() fits in i32 (should be a precondition but adding runtime check)
    if s.len() > i32::MAX as usize {
        return s.len() as i8;  // fallback
    }
    let len: i32 = s.len() as i32;
    
    // Binary search for minimum width
    let mut low: i32 = 1;
    let mut high: i32 = len;
    let mut result: i32 = len;
    
    // Max width (len) always works - everything fits on one line
    assert(k >= 1);
    assert(s@.len() >= 1);
    assert(len >= 1);
    assert(can_format_text(s@, k as int, len as int));
    
    while low <= high
        invariant
            1 <= low,
            low <= len + 1,
            high >= 0,
            high <= len,
            1 <= result,
            result <= len,
            k >= 1,
            s@.len() >= 1,
            can_format_text(s@, k as int, result as int),
            low > 1 ==> !can_format_text(s@, k as int, (low - 1) as int),
        decreases high - low + 1,
    {
        let mid: i32 = low + (high - low) / 2;
        assert(1 <= mid && mid <= len);
        
        // Simulate text formatting to check if width=mid works
        let mut can_fit: bool = true;
        let mut pos: usize = 0;
        let mut lines: i32 = 1;
        let mut current_line: i32 = 0;
        
        while pos < s.len()
            invariant_except_break
                0 <= pos,
                pos <= s.len(),
                lines >= 1,
                current_line >= 0,
                current_line <= mid,
                can_fit ==> (lines <= k as i32 && current_line <= mid),
                !can_fit ==> (lines > k as i32 || current_line > mid),
            ensures
                pos == s.len() || !can_fit,
                can_fit ==> lines <= k as i32,
            decreases s.len() - pos,
        {
            if s[pos] == ' ' || s[pos] == '-' {
                // Potential break point
                if current_line + 1 > mid {
                    // Must break line here
                    lines = lines + 1;
                    if lines > k as i32 {
                        can_fit = false;
                        break;
                    }
                    current_line = 1;
                } else {
                    // Continue on current line
                    current_line = current_line + 1;
                }
            } else {
                // Regular character - must continue on current line
                if current_line + 1 > mid {
                    // Can't fit this character
                    can_fit = false;
                    break;
                }
                current_line = current_line + 1;
            }
            pos = pos + 1;
        }
        
        if can_fit {
            // mid works, try smaller width
            result = mid;
            assert(can_format_text(s@, k as int, mid as int));
            high = mid - 1;
        } else {
            // mid doesn't work, need larger width
            assert(!can_format_text(s@, k as int, mid as int));
            low = mid + 1;
        }
    }
    
    // Convert result to i8
    assert(1 <= result && result <= s.len() as i32);
    assert(result <= i8::MAX as i32);
    result as i8
}
// </vc-code>


}

fn main() {}