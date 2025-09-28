// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    (s.len() == 3 || (s.len() == 4 && s[3] == '\n')) &&
    forall|i: int| 0 <= i < (if s.len() == 4 { 3 } else { s.len() as int }) ==> 
        (s[i] == 'a' || s[i] == 'b' || s[i] == 'c')
}

spec fn get_input_chars(s: Seq<char>) -> Seq<char> {
    if s.len() == 4 { s.subrange(0, 3) } else { s }
}

spec fn is_permutation_of_abc(input_chars: Seq<char>) -> bool {
    input_chars.len() == 3 &&
    (forall|i: int| 0 <= i < input_chars.len() ==> 
        (input_chars[i] == 'a' || input_chars[i] == 'b' || input_chars[i] == 'c')) &&
    input_chars[0] != input_chars[1] && 
    input_chars[1] != input_chars[2] && 
    input_chars[0] != input_chars[2]
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires 
        s@.len() >= 3,
        valid_input(s@),
    ensures 
        result@ == seq!['Y', 'e', 's', '\n'] || result@ == seq!['N', 'o', '\n'],
        result@ == seq!['Y', 'e', 's', '\n'] <==> is_permutation_of_abc(get_input_chars(s@)),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fix by using direct variable access and explicit distinctness check */
{
    let c0 = s[0];
    let c1 = s[1];
    let c2 = s[2];

    let has_a = c0=='a' || c1=='a' || c2=='a';
    let has_b = c0=='b' || c1=='b' || c2=='b';
    let has_c = c0=='c' || c1=='c' || c2=='c';

    let distinct = c0 != c1 && c1 != c2 && c0 != c2;

    if has_a && has_b && has_c && distinct {
        vec!['Y','e','s','\n']
    } else {
        vec!['N','o','\n']
    }
}
// </vc-code>


}

fn main() {}