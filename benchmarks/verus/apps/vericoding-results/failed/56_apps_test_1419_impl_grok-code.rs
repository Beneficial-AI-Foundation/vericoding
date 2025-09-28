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
/* helpers modified by LLM (iteration 2): Added executable helper functions for spec predicates using usize */
fn exec_check_formatting(s: &Vec<char>, k: usize, max_width: usize, pos: usize, lines: usize, current_line: usize) -> (result: bool)
    requires
        k >= 1,
        max_width >= 1,
        s.len() >= 1,
        0 <= pos <= s@.len(),
        lines >= 1,
        current_line >= 0,
    ensures
        result == check_formatting(s@, k as int, max_width as int, pos as int, lines as int, current_line as int),
    decreases s@.len() - pos
{
    if pos == s.len() {
        return lines <= k && current_line <= max_width;
    }
    let ch = s[pos];
    if ch == ' ' || ch == '-' {
        if current_line + 1 > max_width {
            if lines + 1 > k {
                return false;
            } else {
                return exec_check_formatting(s, k, max_width, pos + 1, lines + 1, 1);
            }
        } else {
            let stay = exec_check_formatting(s, k, max_width, pos + 1, lines, current_line + 1);
            let mut break_opt = false;
            if lines < k {
                break_opt = exec_check_formatting(s, k, max_width, pos + 1, lines + 1, 1);
            }
            return stay || break_opt;
        }
    } else {
        if current_line + 1 > max_width {
            return false;
        } else {
            return exec_check_formatting(s, k, max_width, pos + 1, lines, current_line + 1);
        }
    }
}

fn can_format_spec(s: &Vec<char>, k: usize, max_width: usize) -> (result: bool)
    requires
        k >= 1,
        s.len() >= 1,
        max_width >= 1,
    ensures
        result == can_format_text(s@, k as int, max_width as int),
{
    exec_check_formatting(s, k, max_width, 0, 1, 0)
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
/* code modified by LLM (iteration 3): Fixed compilation by casting usize to i8 instead of nat to i8 */
{
    let n_int: usize = s.len();
    proof {
        assert(n_int <= i8::MAX as int);
    }
    let mut low: i8 = 1;
    let mut high: i8 = n_int as i8;
    while low < high
        invariant
            1 <= low <= high,
            (low - 1) as int <= n_int,
            high <= n_int as i8,
            forall |w: int| 1 <= w < low ==> !can_format_text(s@, k as int, w),
            forall |w: int| low as int <= w && w <= n_int as int && can_format_text(s@, k as int, w) ==> w >= low as int,
        decreases (high - low)
    {
        let mid = low + (high - low) / 2;
        if can_format_spec(&s, k as usize, mid as usize) {
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