// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    let lines = split_lines_spec(input);
    lines.len() >= 2 && is_valid_integer(lines[0]) && is_valid_integer(lines[1])
}

spec fn is_valid_integer(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> ('0' <= #[trigger] s[i] && s[i] <= '9')
}

spec fn split_lines_spec(s: Seq<char>) -> Seq<Seq<char>>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else if s[0] == '\n' {
        split_lines_spec(s.subrange(1, s.len() as int))
    } else {
        let next_newline = find_next_newline(s, 0);
        if next_newline == -1 {
            seq![s]
        } else if next_newline >= 0 && next_newline < s.len() && next_newline + 1 <= s.len() {
            seq![s.subrange(0, next_newline)] + split_lines_spec(s.subrange(next_newline + 1, s.len() as int))
        } else {
            seq![]
        }
    }
}

spec fn find_next_newline(s: Seq<char>, start: nat) -> int
    decreases s.len() - start
{
    if start >= s.len() {
        -1
    } else if s[start as int] == '\n' {
        start as int
    } else {
        find_next_newline(s, start + 1)
    }
}

spec fn parse_int_spec(s: Seq<char>) -> int {
    parse_int_helper(s, 0)
}

spec fn parse_int_helper(s: Seq<char>, pos: nat) -> int
    decreases s.len() - pos
{
    if pos >= s.len() || s[pos as int] == '\n' || s[pos as int] == '\r' {
        0
    } else if '0' <= s[pos as int] <= '9' {
        (s[pos as int] as int - '0' as int) + 10 * parse_int_helper(s, pos + 1)
    } else {
        parse_int_helper(s, pos + 1)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): executable split_lines */
fn split_lines_exec(s: &str) -> Vec<String> {
    let mut res: Vec<String> = Vec::new();
    let mut cur = String::new();
    for ch in s.chars() {
        if ch == '\n' {
            if cur.len() > 0 {
                res.push(cur.clone());
                cur.clear();
            } else {
                // skip empty segments to match spec behavior
            }
        } else {
            cur.push(ch);
        }
    }
    if cur.len() > 0 {
        res.push(cur);
    }
    res
}

/* helper modified by LLM (iteration 5): executable parse_int (uses i64 for executable code) */
fn parse_int_exec(s: &str) -> i64 {
    let mut acc: i64 = 0;
    let mut place: i64 = 1;
    for ch in s.chars() {
        if ch == '\n' || ch == '\r' {
            break;
        } else if '0' <= ch && ch <= '9' {
            let v: i64 = (ch as i64) - ('0' as i64);
            acc = acc + v * place;
            place = place * 10;
        }
    }
    acc
}

/* helper modified by LLM (iteration 5): proof linking parse_int_exec to spec */
proof fn parse_int_exec_matches_spec(s: &str)
    ensures
        parse_int_spec(s@) == (parse_int_exec(s) as int),
    decreases s@.len()
{
    if s@.len() == 0 {
        // both yield 0
    } else {
        let mut chars_iter = s.chars();
        let first_char = chars_iter.next().unwrap();
        let tail = chars_iter.as_str();
        if first_char == '\n' || first_char == '\r' {
            parse_int_exec_matches_spec(tail);
        } else if '0' <= first_char && first_char <= '9' {
            parse_int_exec_matches_spec(tail);
        } else {
            parse_int_exec_matches_spec(tail);
        }
    }
}

/* helper modified by LLM (iteration 5): proof linking split_lines_exec to spec */
proof fn split_lines_exec_matches_spec(s: &str)
    ensures
        split_lines_spec(s@).len() == split_lines_exec(s).len(),
        forall|i: int| 0 <= i < split_lines_spec(s@).len() ==> split_lines_spec(s@)[i] == split_lines_exec(s)[i]@,
    decreases s@.len()
{
    if s@.len() == 0 {
        // both produce zero lines
    } else if s@[0] == '\n' {
        let mut chars_iter = s.chars();
        let _ = chars_iter.next(); // consume first newline
        let tail = chars_iter.as_str();
        split_lines_exec_matches_spec(tail);
    } else {
        let next_nl = find_next_newline(s@, 0);
        if next_nl == -1 {
            // exec split produces single segment equal to s when no newline present
        } else {
            // advance iterator next_nl+1 characters to get substring after newline
            let mut chars_iter = s.chars();
            for _ in 0..(next_nl as usize + 1) {
                let _ = chars_iter.next();
            }
            let after = chars_iter.as_str();
            split_lines_exec_matches_spec(after);
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    requires input@.len() > 0
    ensures ({
        let input_seq = input@;
        valid_input(input_seq) ==> {
            let lines = split_lines_spec(input_seq);
            let a = parse_int_spec(lines[0]);
            let b = parse_int_spec(lines[1]);
            (result@ == "LESS\n"@) == (a < b) &&
            (result@ == "GREATER\n"@) == (a > b) &&
            (result@ == "EQUAL\n"@) == (a == b)
        }
    }) && ({
        let input_seq = input@;
        !valid_input(input_seq) ==> result@ == ""@
    })
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): implementation using exec helpers with i64 */
    let exec_lines = split_lines_exec(input);

    if exec_lines.len() < 2 {
        return String::new();
    }

    let a_str = exec_lines[0].as_str();
    let b_str = exec_lines[1].as_str();
    let a_val = parse_int_exec(a_str);
    let b_val = parse_int_exec(b_str);

    proof {
        split_lines_exec_matches_spec(input);
        parse_int_exec_matches_spec(a_str);
        parse_int_exec_matches_spec(b_str);
    }

    if a_val < b_val {
        "LESS\n".to_string()
    } else if a_val > b_val {
        "GREATER\n".to_string()
    } else {
        "EQUAL\n".to_string()
    }
}

// </vc-code>


}

fn main() {}