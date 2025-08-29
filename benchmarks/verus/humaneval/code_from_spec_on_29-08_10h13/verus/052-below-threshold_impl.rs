use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-description>
/*
function_signature: "def below_threshold(numbers: List[Int], threshold: Int) -> bool"
docstring: Return True if all numbers in the list l are below threshold t, and False otherwise.
test_cases:
- input: [[1, 2, 4, 10], 100]
expected_output: True
- input: [[1, 20, 4, 10], 5]
expected_output: False
*/
// </vc-description>

// <vc-spec>
fn below_threshold(numbers: Vec<i32>, threshold: i32) -> (result: bool)
    ensures result == forall|i: int| 0 <= i < numbers.len() ==> numbers@[i] < threshold
// </vc-spec>

// <vc-code>
{
    for i in 0..numbers.len()
        invariant forall|j: int| 0 <= j < i ==> numbers@[j] < threshold
    {
        if numbers[i] >= threshold {
            return false;
        }
    }
    true
}
// </vc-code>

}
fn main() {}