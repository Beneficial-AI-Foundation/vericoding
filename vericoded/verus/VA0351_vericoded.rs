// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_valid_input(s: Seq<char>) -> bool {
    s.len() >= 5 && s[s.len() as int - 1] == '\n'
}

spec fn calculate_result_from_input(s: Seq<char>) -> Seq<char> {
    s /* placeholder implementation */
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires 
        s.len() > 0,
        (exists|i: int| 0 <= i < s.len() as int && s@[i] == '\n'),
        is_valid_input(s@),
    ensures 
        result.len() > 0,
        result@[result.len() as int - 1] == '\n'
// </vc-spec>
// <vc-code>
{
    s
}
// </vc-code>


}

fn main() {}