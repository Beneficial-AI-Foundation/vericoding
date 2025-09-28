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
proof fn lemma_check_formatting_enough_width(s: Seq<char>, k: int, maxw: int, pos: int, lines: int, current_line: int)
    requires
        k >= 1,
        s.len() >= 1,
        0 <= pos <= s.len(),
        lines >= 1,
        current_line >= 0,
        lines <= k,
        maxw >= current_line + (s.len() - pos),
    ensures
        check_formatting(s, k, maxw, pos, lines, current_line),
    decreases s.len() - pos
{
    if pos == s.len() {
        assert(lines <= k);
        assert(current_line <= maxw);
    } else {
        assert(maxw >= current_line + 1 + (s.len() - (pos + 1))) by {
            assert(s.len() - pos == (s.len() - (pos + 1)) + 1);
        };
        if s[pos] == ' ' || s[pos] == '-' {
            assert(current_line + 1 <= maxw);
            lemma_check_formatting_enough_width(s, k, maxw, pos + 1, lines, current_line + 1);
        } else {
            assert(current_line + 1 <= maxw);
            lemma_check_formatting_enough_width(s, k, maxw, pos + 1, lines, current_line + 1);
        }
    }
}

proof fn lemma_can_format_at_full_length(s: Seq<char>, k: int)
    requires
        k >= 1,
        s.len() >= 1,
    ensures
        can_format_text(s, k, s.len()),
{
    lemma_check_formatting_enough_width(s, k, s.len(), 0, 1, 0);
}

fn check_formatting_rec_int(s: &Vec<char>, k: int, max_width: int, pos: int, lines: int, current_line: int) -> (r: bool)
    requires
        k >= 1,
        s.len() >= 1,
        max_width >= 1,
        0 <= pos <= s.len() as int,
        lines >= 1,
        current_line >= 0,
    ensures
        r == check_formatting(s@, k, max_width, pos, lines, current_line),
    decreases s.len() as int - pos
{
    if pos == s.len() as int {
        return lines <= k && current_line <= max_width;
    } else {
        let c = s[pos as usize];
        if c == ' ' || c == '-' {
            if current_line + 1 > max_width {
                if lines + 1 > k {
                    return false;
                } else {
                    return check_formatting_rec_int(s, k, max_width, pos + 1, lines + 1, 1);
                }
            } else {
                let cont = check_formatting_rec_int(s, k, max_width, pos + 1, lines, current_line + 1);
                if cont {
                    return true;
                } else {
                    if lines < k {
                        return check_formatting_rec_int(s, k, max_width, pos + 1, lines + 1, 1);
                    } else {
                        return false;
                    }
                }
            }
        } else {
            if current_line + 1 > max_width {
                return false;
            } else {
                return check_formatting_rec_int(s, k, max_width, pos + 1, lines, current_line + 1);
            }
        }
    }
}

fn can_format_text_exec_int(s: &Vec<char>, k: int, max_width: int) -> (r: bool)
    requires
        k >= 1,
        s.len() >= 1,
        max_width >= 1,
    ensures
        r == can_format_text(s@, k, max_width),
{
    check_formatting_rec_int(s, k, max_width, 0, 1, 0)
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
    /* code modified by LLM (iteration 2): fixed quantifier syntax and strengthened invariant for minimality */
    let kk: int = k as int;
    let n: int = s.len() as int;
    let mut w: int = 1;
    let mut ans: int = 1;
    let mut found: bool = false;
    while w <= n
        invariant
            k >= 1,
            s.len() >= 1,
            1 <= w <= n + 1,
            1 <= ans <= n,
            found ==> can_format_text(s@, kk, ans),
            found ==> forall|j: int| 1 <= j && j < ans ==> !can_format_text(s@, kk, j),
            !found ==> forall|j: int| 1 <= j && j < w ==> !can_format_text(s@, kk, j),
        decreases n - w + 1
    {
        let ok = can_format_text_exec_int(&s, kk, w);
        if ok {
            if !found {
                // capture facts before changing found/ans
                proof {
                    assert(ok == can_format_text(s@, kk, w));
                    assert(!found);
                    assert(forall|j: int| 1 <= j && j < w ==> !can_format_text(s@, kk, j));
                }
                found = true;
                ans = w;
                proof {
                    // establish invariants for found-state
                    assert(ok == can_format_text(s@, kk, w));
                    assert(can_format_text(s@, kk, w));
                    assert(ans == w);
                    assert(can_format_text(s@, kk, ans));
                    // from previously asserted property with bound w and ans == w
                    assert(forall|j: int| 1 <= j && j < w ==> !can_format_text(s@, kk, j));
                    assert(forall|j: int| 1 <= j && j < ans ==> !can_format_text(s@, kk, j));
                }
            }
        }
        w = w + 1;
    }
    proof {
        lemma_can_format_at_full_length(s@, kk);
        if !found {
            assert(1 <= n);
            assert(n < w);
            assert(!can_format_text(s@, kk, n));
            assert(false);
        }
    }
    let result: i8 = ans as i8;
    result
}
// </vc-code>


}

fn main() {}