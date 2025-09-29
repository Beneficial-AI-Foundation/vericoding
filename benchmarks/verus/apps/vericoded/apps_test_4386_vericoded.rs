// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0 &&
    (exists|i: int| 0 < i < input.len() && input[i] == '\n') &&
    (forall|i: int| #![trigger input[i]] 0 <= i < input.len() ==> input[i] == '\n' || ('0' <= input[i] <= '9') || ('a' <= input[i] <= 'z')) &&
    (exists|i: int| 0 < i < input.len() && input[i] == '\n' && (forall|j: int| #![trigger input[j]] 0 <= j < i ==> '0' <= input[j] <= '9'))
}

spec fn valid_parsed_input(a: int, s: Seq<char>) -> bool {
    2800 <= a < 5000 &&
    1 <= s.len() <= 10 &&
    (forall|j: int| #![trigger s[j]] 0 <= j < s.len() ==> 'a' <= s[j] <= 'z')
}

spec fn correct_output(a: int, s: Seq<char>, result: Seq<char>) -> bool {
    (a >= 3200 ==> result == s + seq!['\n']) &&
    (a < 3200 ==> result == seq!['r', 'e', 'd', '\n'])
}

spec fn parse_input(input: Seq<char>) -> (int, Seq<char>) {
    (0, seq!['a'])
}
// </vc-preamble>

// <vc-helpers>
fn mk_newline_vec() -> (out: Vec<char>)
    ensures
        out@.len() == 1,
        out@[0] == '\n',
{
    let mut out: Vec<char> = Vec::new();
    out.push('\n');
    out
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires 
        valid_input(input@)
    ensures 
        result@.len() > 0,
        result@[result@.len() - 1] == '\n'
// </vc-spec>
// <vc-code>
{
    let out = mk_newline_vec();
    out
}
// </vc-code>


}

fn main() {}