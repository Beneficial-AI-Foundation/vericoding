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
/* helper modified by LLM (iteration 5): no helper fixes needed after fixing main code */
spec fn find_min_satisfying_width(s: Seq<char>, k: int, min_width: int, max_width: int) -> int
    recommends
        k >= 1,
        s.len() >= 1,
        min_width >= 1,
        min_width <= max_width + 1 // permit max_width + 1 for the 'not found' case
    decreases max_width - min_width
{
    if min_width > max_width {
        max_width + 1
    } else {
        let mid = (min_width + max_width) / 2;
        if can_format_text(s, k, mid) {
            find_min_satisfying_width(s, k, min_width, mid - 1)
        } else {
            find_min_satisfying_width(s, k, mid + 1, max_width)
        }
    }
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
/* code modified by LLM (iteration 5): removed unnecessary explicit cast in trusted block; Verus is smart enough to handle the int-to-i8 conversion and check for overflows automatically. */
{
    let ghost s_len: int = s.len() as int;
    let ghost k_int: int = k as int;

    // The minimum possible width is 1.
    // The maximum possible width is the length of the string, as each character could be on its own line.
    let ghost min_width_val: int = 1;
    let ghost max_width_val: int = s_len;

    let ghost result_width = find_min_satisfying_width(s@, k_int, min_width_val, max_width_val);

    proof {
        assert(can_format_text(s@, k_int, s_len)); // A width of s_len is always a valid format
        // This assertion is critical for proving result_width <= s_len.
        // If can_format_text(s@, k_int, s_len) is true, then find_min_satisfying_width
        // will always return a width value less than or equal to s_len,
        // because s_len is within the search range and satisfies the condition.
    }

    // Since we know a solution exists, result_width must be <= max_width_val
    // In the event that no formatting is possible, find_min_satisfying_width might return max_width_val + 1
    // However, the problem statement implies a solution always exists within the constraints.
    // A single character 'a' with k=1 has a solution of width 1.
    // A string "a-b" with k=2 can be formatted with width 1. Each character on its own line.
    // Or with width 3. "a-b" on one line.
    // A string "abc" with k=1 has a solution of width 3.

    // The range of 'a' to 'b' for binary search is from 1 to s.len().
    // The problem statement guarantees k >= 1 and s.len() >= 1, so a solution always exists.
    // For example, if max_width = s.len(), then each character can be on its own line if needed,
    // or the entire string can fit on one line. The `can_format_text` would return true.
    // Therefore, `find_min_satisfying_width` will always find a result at most `s.len()`.
    assert(result_width <= s_len);

    // We are guaranteed that result_width will be between 1 and s.len() (inclusive).
    // Since s_len is an int, result_width is an int.
    // The return type is i8.
    let final_result: i8 = result_width;
    final_result
}
// </vc-code>


}

fn main() {}