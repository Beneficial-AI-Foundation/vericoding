// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() >= 1 && s.len() <= 100 && forall|i: int| 0 <= i < s.len() ==> 'a' <= s[i] && s[i] <= 'z'
}

spec fn valid_output(s: Seq<char>, result: Seq<char>) -> bool {
    result.len() == s.len() && forall|i: int| 0 <= i < result.len() ==> result[i] == 'x'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): named return value for ensures clause */
fn char_to_x(c: char) -> (x_char: char)
    ensures x_char == 'x'
{
    'x'
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires valid_input(s@)
    ensures valid_output(s@, result@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): no changes needed */
{
    let mut result_vec = Vec::new();
    let mut i = 0;

    while i < s.len()
        invariant
            i <= s.len(),
            result_vec.len() == i,
            forall|j: int| 0 <= j < i ==> result_vec@[j] == 'x',
            valid_input(s@),
        decreases s.len() - i
    {
        result_vec.push(char_to_x(s[i]));
        i = i + 1;
    }
    result_vec
}
// </vc-code>


}

fn main() {}