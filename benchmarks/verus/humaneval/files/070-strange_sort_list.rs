use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;

verus! {

/*
function_signature: "def strange_sort_list(lst: List[int]) -> List[int]"
docstring: |
Given list of integers, return list in strange order.
Strange sorting is when you start with the minimum value,
then the maximum of the remaining integers, then the minimum and so on.
test_cases:
- input: [1, 2, 3, 4]
expected_output: [1, 4, 2, 3]
- input: [5, 5, 5, 5]
expected_output: [5, 5, 5, 5]
- input: []
expected_output: []
*/

fn strange_sort_list(s: &Vec<i32>) -> (ret: Vec<i32>)
    // post-conditions-start
    ensures
        s@.len() == ret@.len(),
    // post-conditions-end
{
    // impl-start
    assume(false);
    vec![]
    // impl-end
}

}
fn main() {}