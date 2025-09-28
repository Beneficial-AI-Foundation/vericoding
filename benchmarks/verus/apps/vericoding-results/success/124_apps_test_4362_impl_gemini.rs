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
/* helper modified by LLM (iteration 2): added decreases clause to loop */
fn check_all_lowercase(s: &Vec<char>) -> (result: bool)
    ensures result == all_lowercase(s@),
{
    if s.len() == 0 {
        return false;
    }
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < i ==> is_lowercase_letter(s@[j]),
        decreases s.len() - i
    {
        let c = s[i];
        if !('a' <= c && c <= 'z') {
            return false;
        }
        i = i + 1;
    }
    true
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
/* code modified by LLM (iteration 2): implemented logic using helper function */
{
    let is_all_lowercase = check_all_lowercase(&input);
    if is_all_lowercase {
        vec!['a']
    } else {
        vec!['A']
    }
}
// </vc-code>


}

fn main() {}