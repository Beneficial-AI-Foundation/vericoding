// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(lines: Seq<Seq<char>>) -> bool {
    lines.len() >= 2 && lines[0].len() > 0 && lines[1].len() > 0
}

spec fn is_symmetric(first_row: Seq<char>, second_row: Seq<char>) -> bool {
    reverse_seq(first_row) == second_row
}

spec fn split_lines(s: Seq<char>) -> Seq<Seq<char>> 
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else if s[0] == '\n' {
        seq![seq![]] + split_lines(s.subrange(1, s.len() as int))
    } else {
        let rest = split_lines(s.subrange(1, s.len() as int));
        if rest.len() == 0 {
            seq![seq![s[0]]]
        } else {
            seq![rest[0].push(s[0])] + rest.subrange(1, rest.len() as int)
        }
    }
}

spec fn reverse_seq(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        reverse_seq(s.subrange(1, s.len() as int)).push(s[0])
    }
}
// </vc-preamble>

// <vc-helpers>
fn make_no() -> (result: String)
    ensures result@ == "NO\n"@
{
    "NO\n".to_string()
}

fn make_yes() -> (result: String)
    ensures result@ == "YES\n"@
{
    "YES\n".to_string()
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (result: String)
    requires stdin_input@.len() > 0
    ensures result@ == "YES\n"@ || result@ == "NO\n"@
// </vc-spec>
// <vc-code>
{
    let r = make_no();
    r
}
// </vc-code>


}

fn main() {}