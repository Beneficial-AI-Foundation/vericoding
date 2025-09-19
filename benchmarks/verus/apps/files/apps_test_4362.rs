// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_lowercase_letter(c: char) -> bool {
    'a' <= c && c <= 'z'
}

spec fn all_lowercase(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> is_lowercase_letter(s[i])
}

spec fn valid_output(result: Seq<char>) -> bool {
    result =~= seq!['A'] || result =~= seq!['a']
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    ensures 
        valid_output(result@) &&
        (all_lowercase(input@) ==> result@ =~= seq!['a']) &&
        ((input@.len() == 0 || !all_lowercase(input@)) ==> result@ =~= seq!['A'])
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}