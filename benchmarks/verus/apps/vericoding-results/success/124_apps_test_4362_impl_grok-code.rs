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
/* helper modified by LLM (iteration 3): added decreases clause to while loop to fix verification error */
fn is_all_lowercase(v: &Vec<char>) -> (b: bool)
    ensures
        b == all_lowercase(v@),
{
    if v.len() == 0 {
        false
    } else {
        let mut i = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                forall|j: int| 0 <= j < i ==> ('a' <= v@[j] && v@[j] <= 'z'),
            decreases v.len() - i
        {
            if !('a' <= v[i] && v[i] <= 'z') {
                return false;
            }
            i = i + 1;
        }
        true
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    ensures 
        valid_output(result@) &&
        (all_lowercase(input@) ==> result@ =~= seq!['a']) &&
        ((input@.len() == 0 || !all_lowercase(input@)) ==> result@ =~= seq!['A'])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): implement solve function by calling helper to check if input is all lowercase and return 'a' or 'A' accordingly */
{
    let b = is_all_lowercase(&input);
    if input.len() > 0 && b {
        vec!['a']
    } else {
        vec!['A']
    }
}
// </vc-code>


}

fn main() {}