// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_hard_to_enter(s: Seq<char>) -> bool
    recommends s.len() == 4
{
    s[0] == s[1] || s[1] == s[2] || s[2] == s[3]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Converted spec function to executable helper for checking if password is hard to enter */
fn is_hard_to_enter_exec(s: &Vec<char>) -> (result: bool)
    requires
        s@.len() == 4,
    ensures
        result <==> is_hard_to_enter(s@)
{
    s[0] == s[1] || s[1] == s[2] || s[2] == s[3]
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires s@.len() == 4
    ensures 
        result@.len() > 0,
        (result@ == seq!['B', 'a', 'd'] <==> is_hard_to_enter(s@)),
        (result@ == seq!['G', 'o', 'o', 'd'] <==> !is_hard_to_enter(s@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Implemented main logic to determine password hardness and return appropriate string */
    let cond = is_hard_to_enter_exec(&s);
    let mut result = Vec::new();
    if cond {
        result.push('B');
        result.push('a');
        result.push('d');
    } else {
        result.push('G');
        result.push('o');
        result.push('o');
        result.push('d');
    }
    proof {
        assert(cond <==> is_hard_to_enter(s@));
        if cond {
            assert(result@ == seq!['B', 'a', 'd']);
            assert(is_hard_to_enter(s@));
        } else {
            assert(result@ == seq!['G', 'o', 'o', 'd']);
            assert(!is_hard_to_enter(s@));
        }
    }
    result
}
// </vc-code>


}

fn main() {}