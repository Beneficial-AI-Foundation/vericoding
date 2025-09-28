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
/* helper modified by LLM (iteration 3): add helper to bridge spec and exec */
exec fn is_hard_to_enter_exec(s: &Vec<char>) -> (result: bool)
    requires s@.len() == 4
    ensures result == is_hard_to_enter(s@)
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
/* code modified by LLM (iteration 3): call exec helper instead of spec function */
{
    let hard_to_enter = is_hard_to_enter_exec(&s);
    if hard_to_enter {
        return vec!['B', 'a', 'd'];
    } else {
        return vec!['G', 'o', 'o', 'd'];
    }
}
// </vc-code>


}

fn main() {}