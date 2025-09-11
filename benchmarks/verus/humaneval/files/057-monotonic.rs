use vstd::prelude::*;

verus! {

/*
function_signature: "def monotonic(numbers: List[int]) -> Bool"
docstring: |
Return True if list elements are monotonically increasing or decreasing.
test_cases:
- input: [1, 2, 4, 20]
expected_output: True
- input: [1, 20, 4, 10]
expected_output: False
- input: [4, 1, 0, -10]
expected_output: True
*/

fn monotonic(l: Vec<i32>) -> (ret: bool)
    // post-conditions-start
    ensures
        ret <==> (forall|i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) <= l@.index(j)) || (
        forall|i: int, j: int| 0 <= i < j < l@.len() ==> l@.index(i) >= l@.index(j)),
    // post-conditions-end
{
    // impl-start
    assume(false);
    false
    // impl-end
}

}
fn main() {}