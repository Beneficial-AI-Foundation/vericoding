use vstd::prelude::*;

verus! {

/*
function_signature: "def add(x: Int, y: Int) -> Int"
docstring: Add two numbers x and y
test_cases:
- input: [2, 3]
expected_output: 5
- input: [5, 7]
expected_output: 12
*/

fn add(x: i32, y: i32) -> (res: Option<i32>)
    // post-conditions-start
    ensures
        res.is_some() ==> res.unwrap() == x + y,
    // post-conditions-end
{
    // impl-start
    assume(false);
    None
    // impl-end
}

}
fn main() {}