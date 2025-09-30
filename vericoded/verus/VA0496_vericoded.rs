// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> 'a' <= s[i] && s[i] <= 'z'
}

spec fn correct_plural(s: Seq<char>, result: Seq<char>) -> bool {
    if s.len() > 0 && s[s.len() - 1] == 's' {
        result == s + seq!['e', 's']
    } else {
        result == s + seq!['s']
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(s: &Vec<char>) -> (result: Vec<char>)
    requires valid_input(s@)
    ensures correct_plural(s@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added proof block to verify postcondition */
    let mut result = s.clone();
    if s[s.len() - 1] == 's' {
        result.push('e');
        result.push('s');
    } else {
        result.push('s');
    }
    proof {
        if s[s.len() - 1] == 's' {
            assert(result@ == s@ + seq!['e', 's']);
        } else {
            assert(result@ == s@ + seq!['s']);
        }
        assert(correct_plural(s@, result@));
    }
    result
}
// </vc-code>


}

fn main() {}