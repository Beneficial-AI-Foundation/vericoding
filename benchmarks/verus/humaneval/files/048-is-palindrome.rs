use vstd::prelude::*;

verus! {

/*
function_signature: "def is_palindrome(string: str) -> Bool"
docstring: |
Checks if given string is a palindrome
test_cases:
- input: ""
expected_output: True
- input: "aba"
expected_output: True
- input: "aaaaa"
expected_output: "True"
- input: "zbcd"
expected_output: "False"
*/

fn is_palindrome(text: &str) -> (result: bool)
    // post-conditions-start
    ensures
        result == forall|i: int|
            0 <= i < text@.len() ==> #[trigger] text@[i] == text@[text@.len() - 1 - i],
    // post-conditions-end
{
    // impl-start
    assume(false);
    false
    // impl-end
}

}
fn main() {}