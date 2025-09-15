// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0 &&
    (exists|i: int| 0 < i < input.len() && input[i] == '\n') &&
    (forall|i: int| 0 <= i < input.len() ==> input[i] == '\n' || ('0' <= input[i] <= '9') || ('a' <= input[i] <= 'z')) &&
    (exists|i: int| 0 < i < input.len() && input[i] == '\n' && (forall|j: int| 0 <= j < i ==> '0' <= input[j] <= '9'))
}

spec fn valid_parsed_input(a: int, s: Seq<char>) -> bool {
    2800 <= a < 5000 &&
    1 <= s.len() <= 10 &&
    (forall|j: int| 0 <= j < s.len() ==> 'a' <= s[j] <= 'z')
}

spec fn correct_output(a: int, s: Seq<char>, result: Seq<char>) -> bool {
    (a >= 3200 ==> result == s + seq!['\n']) &&
    (a < 3200 ==> result == seq!['r', 'e', 'd', '\n'])
}

spec fn parse_input(input: Seq<char>) -> (int, Seq<char>) {
    (0, Seq::<char>::empty())
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: Seq<char>) -> (result: Seq<char>)
    requires 
        valid_input(input) &&
        (exists|a: int, s: Seq<char>| 
            parse_input(input) == (a, s) && valid_parsed_input(a, s))
    ensures 
        (exists|a: int, s: Seq<char>| 
            parse_input(input) == (a, s) && 
            valid_parsed_input(a, s) &&
            correct_output(a, s, result)) &&
        result.len() > 0 &&
        result[result.len()-1] == '\n' &&
        ((exists|a: int, s: Seq<char>| 
            parse_input(input) == (a, s) && a >= 3200) ==> 
            (exists|s: Seq<char>| result == s + seq!['\n'] && 1 <= s.len() <= 10 && (forall|j: int| 0 <= j < s.len() ==> 'a' <= s[j] <= 'z'))) &&
        ((exists|a: int, s: Seq<char>| 
            parse_input(input) == (a, s) && a < 3200) ==> result == seq!['r', 'e', 'd', '\n'])
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}