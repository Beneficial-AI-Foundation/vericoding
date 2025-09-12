// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_lowercase_letter(c: char) -> bool {
    'a' <= c && c <= 'z'
}

spec fn all_lowercase(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> is_lowercase_letter(s[i])
}

spec fn valid_output(result: Seq<char>) -> bool {
    result =~= seq!['A'] || result =~= seq!['a']
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Seq<char>) -> (result: Seq<char>)
    ensures 
        valid_output(result) &&
        (all_lowercase(input) ==> result =~= seq!['a']) &&
        ((input.len() == 0 || !all_lowercase(input)) ==> result =~= seq!['A'])
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}