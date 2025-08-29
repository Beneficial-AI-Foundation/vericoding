use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn has_pair_sum_to_zero(numbers: Seq<int>) -> bool {
    exists|i: int, j: int| 0 <= i < numbers.len() && 0 <= j < numbers.len() && i != j && numbers[i] + numbers[j] == 0
}
// </vc-helpers>

// <vc-description>
/*
function_signature: "def pairs_sum_to_zero(numbers: List[int]) -> Bool"
docstring: |
pairs_sum_to_zero takes a list of integers as an input.
it returns True if there are two distinct elements in the list that
sum to zero, and False otherwise.
test_cases:
- input: [1, 3, 5, 0]
expected_output: False
- input: [1, 3, -2, 1]
expected_output: False
- input: [1]
expected_output: False
- input: [2, 4, -5, 3, 5, 7]
expected_output: True
*/
// </vc-description>

// <vc-spec>
fn pairs_sum_to_zero(numbers: Vec<i32>) -> (result: bool)
    ensures result == has_pair_sum_to_zero(numbers@)
// </vc-spec>

// <vc-code>
{
    let len = numbers.len();
    for i in 0..len
        invariant forall|ii: int, jj: int| 0 <= ii < i && 0 <= jj < len && ii != jj ==> numbers@[ii] + numbers@[jj] != 0
    {
        for j in 0..len
            /* code modified by LLM (iteration 5): added proper curly braces for invariant block */
            invariant forall|ii: int, jj: int| 0 <= ii < i && 0 <= jj < len && ii != jj ==> numbers@[ii] + numbers@[jj] != 0,
            invariant forall|jj: int| 0 <= jj < j && i != jj ==> numbers@[i as int] + numbers@[jj] != 0,
        {
            if i != j && numbers[i] + numbers[j] == 0 {
                proof {
                    assert(numbers@[i as int] + numbers@[j as int] == 0);
                    assert(i as int != j as int);
                    assert(0 <= i as int < numbers@.len() && 0 <= j as int < numbers@.len());
                }
                return true;
            }
        }
    }
    
    proof {
        assert(forall|i: int, j: int| 0 <= i < numbers@.len() && 0 <= j < numbers@.len() && i != j ==> numbers@[i] + numbers@[j] != 0);
        assert(!has_pair_sum_to_zero(numbers@));
    }
    
    false
}
// </vc-code>

}
fn main() {}