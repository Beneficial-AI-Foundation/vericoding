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
/* helper modified by LLM (iteration 2): [added explicit proof body to helper lemma] */
proof fn lemma_valid_input_properties(s: Seq<char>)
    requires
        valid_input(s),
    ensures
        get_input_chars(s).len() == 3,
        forall|i: int| 0 <= i < 3 ==> 
            (get_input_chars(s)[i] == 'a' || get_input_chars(s)[i] == 'b' || get_input_chars(s)[i] == 'c'),
{
    let input_chars = get_input_chars(s);
    if s.len() == 4 {
        assert(input_chars =~= s.subrange(0, 3));
    } else {
        assert(s.len() == 3);
        assert(input_chars =~= s);
    }
}

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
{
    /* code modified by LLM (iteration 2): [wrapped lemma call in proof block to fix compilation bug] */
    proof {
        lemma_valid_input_properties(s@);
    }

    if s[0] != s[1] && s[1] != s[2] && s[0] != s[2] {
        vec!['Y', 'e', 's', '\n']
    } else {
        vec!['N', 'o', '\n']
    }
}
// </vc-code>


}

fn main() {}