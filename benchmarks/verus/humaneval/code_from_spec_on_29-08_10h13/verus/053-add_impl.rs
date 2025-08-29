use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-description>
/*
function_signature: "def add(x: Int, y: Int) -> Int"
docstring: Add two numbers x and y
test_cases:
- input: [2, 3]
expected_output: 5
- input: [5, 7]
expected_output: 12
*/
// </vc-description>

// <vc-spec>
fn add(x: i32, y: i32) -> (res: Option<i32>)
    // post-conditions-start
    ensures
        res.is_some() ==> res.unwrap() == x + y,
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    // impl-start
    match x.checked_add(y) {
        Some(sum) => Some(sum),
        None => None,
    }
    // impl-end
}
// </vc-code>

}
fn main() {}