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
/* helper modified by LLM (iteration 5): fixed postcondition proof by correcting lemma invocation */
proof fn lemma_can_format_monotonic(s: Seq<char>, k: int, w1: int, w2: int)
    requires
        k >= 1,
        s.len() >= 1,
        w1 >= 1,
        w2 >= w1,
        can_format_text(s, k, w1),
    ensures can_format_text(s, k, w2)
{
    lemma_check_formatting_monotonic(s, k, w1, w2, 0, 1, 0);
}

proof fn lemma_check_formatting_monotonic(s: Seq<char>, k: int, w1: int, w2: int, pos: int, lines: int, current_line: int)
    requires
        k >= 1,
        s.len() >= 1,
        w1 >= 1,
        w2 >= w1,
        0 <= pos <= s.len(),
        lines >= 1,
        current_line >= 0,
        check_formatting(s, k, w1, pos, lines, current_line),
    ensures check_formatting(s, k, w2, pos, lines, current_line)
    decreases s.len() - pos
{
    if pos == s.len() {
    } else {
        if s[pos] == ' ' || s[pos] == '-' {
            if current_line + 1 > w1 {
                if lines + 1 <= k {
                    lemma_check_formatting_monotonic(s, k, w1, w2, pos + 1, lines + 1, 1);
                }
            } else {
                if check_formatting(s, k, w1, pos + 1, lines, current_line + 1) {
                    lemma_check_formatting_monotonic(s, k, w1, w2, pos + 1, lines, current_line + 1);
                } else if lines < k {
                    lemma_check_formatting_monotonic(s, k, w1, w2, pos + 1, lines + 1, 1);
                }
            }
        } else {
            if current_line + 1 <= w1 {
                lemma_check_formatting_monotonic(s, k, w1, w2, pos + 1, lines, current_line + 1);
            }
        }
    }
}

proof fn lemma_min_width_exists(s: Seq<char>, k: int)
    requires
        k >= 1,
        s.len() >= 1,
    ensures can_format_text(s, k, s.len() as int)
{
    lemma_check_formatting_trivial(s, k, 0, 1, 0);
}

proof fn lemma_check_formatting_trivial(s: Seq<char>, k: int, pos: int, lines: int, current_line: int)
    requires
        k >= 1,
        s.len() >= 1,
        0 <= pos <= s.len(),
        lines >= 1,
        current_line >= 0,
    ensures check_formatting(s, k, s.len() as int, pos, lines, current_line)
    decreases s.len() - pos
{
    if pos == s.len() {
    } else {
        if pos + 1 == s.len() {
            lemma_check_formatting_trivial(s, k, pos + 1, lines, current_line + 1);
        } else {
            lemma_check_formatting_trivial(s, k, pos + 1, lines, current_line + 1);
        }
    }
}

fn can_format_text_check(k: i8, s: &Vec<char>, max_width: i8) -> (result: bool)
    requires
        k >= 1,
        s.len() >= 1,
        max_width >= 1,
    ensures result == can_format_text(s@, k as int, max_width as int)
{
    check_formatting_impl(s, k, max_width, 0, 1, 0)
}

fn check_formatting_impl(s: &Vec<char>, k: i8, max_width: i8, pos: usize, lines: i8, current_line: i8) -> (result: bool)
    requires
        k >= 1,
        s.len() >= 1,
        max_width >= 1,
        pos <= s.len(),
        lines >= 1,
        current_line >= 0,
        lines <= 127,
        current_line <= 127,
        max_width <= 127,
    ensures result == check_formatting(s@, k as int, max_width as int, pos as int, lines as int, current_line as int)
    decreases s.len() - pos
{
    if pos == s.len() {
        lines <= k && current_line <= max_width
    } else {
        let c = s[pos];
        if c == ' ' || c == '-' {
            if current_line < max_width {
                check_formatting_impl(s, k, max_width, pos + 1, lines, current_line + 1) ||
                (lines < k && check_formatting_impl(s, k, max_width, pos + 1, lines + 1, 1))
            } else {
                if lines < k {
                    check_formatting_impl(s, k, max_width, pos + 1, lines + 1, 1)
                } else {
                    false
                }
            }
        } else {
            if current_line < max_width {
                check_formatting_impl(s, k, max_width, pos + 1, lines, current_line + 1)
            } else {
                false
            }
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
{
    /* code modified by LLM (iteration 5): added bounds checking and proper initialization */
    if s.len() > 127 {
        return 127;
    }
    
    let mut low: i8 = 1;
    let mut high: i8 = s.len() as i8;
    
    proof {
        lemma_min_width_exists(s@, k as int);
    }
    
    while low < high
        invariant
            1 <= low <= high,
            high <= s@.len(),
            high <= 127,
            can_format_text(s@, k as int, high as int),
            low > 1 ==> !can_format_text(s@, k as int, (low - 1) as int),
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        
        if can_format_text_check(k, &s, mid) {
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