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
    if s[0] == s[1] || s[1] == s[2] || s[2] == s[3] {
        let mut result = Vec::new();
        result.push('B');
        result.push('a');
        result.push('d');
        proof {
            assert(result@.len() == 3);
            assert(result@ == seq!['B', 'a', 'd']);
            assert(is_hard_to_enter(s@));
        }
        result
    } else {
        let mut result = Vec::new();
        result.push('G');
        result.push('o');
        result.push('o');
        result.push('d');
        proof {
            assert(result@.len() == 4);
            assert(result@ == seq!['G', 'o', 'o', 'd']);
            assert(!is_hard_to_enter(s@));
        }
        result
    }
}
// </vc-code>


}

fn main() {}