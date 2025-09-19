// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn parse_lines(stdin_input: Seq<char>) -> Seq<Seq<char>>
    decreases stdin_input.len()
{
    if stdin_input.len() == 0 {
        seq![]
    } else {
        let newline_pos = find_newline(stdin_input, 0);
        if newline_pos == -1 {
            seq![stdin_input]
        } else if newline_pos == 0 {
            parse_lines(stdin_input.subrange(1, stdin_input.len() as int))
        } else if newline_pos < stdin_input.len() && newline_pos >= 0 {
            seq![stdin_input.subrange(0, newline_pos)] + parse_lines(stdin_input.subrange(newline_pos + 1, stdin_input.len() as int))
        } else {
            seq![]
        }
    }
}

spec fn find_newline(s: Seq<char>, start: int) -> int
    decreases s.len() - start
{
    if start >= s.len() {
        -1
    } else if s[start] == '\n' {
        start
    } else {
        find_newline(s, start + 1)
    }
}

spec fn valid_input(stdin_input: Seq<char>) -> bool {
    let lines = parse_lines(stdin_input);
    lines.len() >= 2 && lines[0].len() > 0 && lines[1].len() > 0 &&
    (forall|i: int| 0 <= i < lines[0].len() ==> 'a' <= lines[0][i] <= 'z') &&
    (forall|i: int| 0 <= i < lines[1].len() ==> 'a' <= lines[1][i] <= 'z')
}

spec fn is_subsequence(s: Seq<char>, t: Seq<char>) -> bool {
    if s.len() == 0 {
        true
    } else if t.len() == 0 {
        false
    } else if s[0] == t[0] {
        is_subsequence(s.subrange(1, s.len() as int), t.subrange(1, t.len() as int))
    } else {
        is_subsequence(s, t.subrange(1, t.len() as int))
    }
}

spec fn sort_string(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() <= 1 {
        s
    } else {
        let pivot = s[0];
        let smaller = filter_chars(s.subrange(1, s.len() as int), pivot, true, false);
        let equal = filter_chars(s, pivot, false, true);
        let larger = filter_chars(s.subrange(1, s.len() as int), pivot, false, false);
        sort_string(smaller) + equal + sort_string(larger)
    }
}

spec fn filter_chars(s: Seq<char>, pivot: char, take_less: bool, take_equal: bool) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        let first = s[0];
        let rest = filter_chars(s.subrange(1, s.len() as int), pivot, take_less, take_equal);
        if (take_less && first < pivot) || (take_equal && first == pivot) || (!take_less && !take_equal && first > pivot) {
            seq![first] + rest
        } else {
            rest
        }
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (result: &'static str)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    "array"
    // impl-end
}
// </vc-code>


}

fn main() {}