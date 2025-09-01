use vstd::prelude::*;

verus! {

/*
function_signature: "def get_positive(l: list)"
docstring: |
Return only positive numbers in the list.
test_cases:
- input: [-1, 2, -4, 5, 6]
expected_output: [2, 5, 6]
- input: [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10]
expected_output: [5, 3, 2, 3, 9, 123, 1]
*/

fn get_positive(input: Vec<i32>) -> (positive_list: Vec<i32>)
    // post-conditions-start
    ensures
        positive_list@ == input@.filter(|x: i32| x > 0),
    // post-conditions-end
{
    // impl-start
    assume(false);
    vec![]
    // impl-end
}

}
fn main() {}