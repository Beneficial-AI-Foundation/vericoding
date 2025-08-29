use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-description>
/*
function_signature: "def strlen(string: str) -> int"
docstring: |
Return length of given string
test_cases:
- input: ""
expected_output: 0
- input: "abc"
expected_output: 3
*/
// </vc-description>

// <vc-spec>
fn strlen(string: &str) -> (result: usize)
    ensures result == string@.len()
// </vc-spec>

// <vc-code>
{
    /* code modified by LLM (iteration 5): convert nat to usize for return type */
    string@.len() as usize
}
// </vc-code>

}
fn main() {}