use vstd::prelude::*;

verus! {

// <vc-helpers>
lemma lemma_push_preserves_invariant(result: Vec<i32>, l: Vec<i32>, i: usize, new_val: i32)
    requires
        i < l.len(),
        result.len() == i,
        forall|j: int| 0 <= j < i ==> #[trigger] result[j] == l[j] + 1,
        new_val == l[i] + 1,
    ensures
        {
            let new_result = result.push(new_val);
            &&& new_result.len() == i + 1
            &&& forall|j: int| 0 <= j < i + 1 ==> #[trigger] new_result[j] == l[j] + 1
        }
{
    let new_result = result.push(new_val);
    assert(new_result.len() == result.len() + 1);
    assert(new_result.len() == i + 1);
    
    assert forall|j: int| 0 <= j < i + 1 implies #[trigger] new_result[j] == l[j] + 1 by {
        if j < i {
            assert(new_result[j] == result[j]);
            assert(result[j] == l[j] + 1);
        } else if j == i {
            assert(new_result[j] == new_val);
            assert(new_val == l[j] + 1);
        }
    };
}
// </vc-helpers>

// <vc-description>
/*
function_signature: "def incr_list(numbers: List[Int]) -> List[Int]"
docstring: |
incr_list takes a list of integers as input and returns a new list
where each element is incremented by 1.
test_cases:
- input: []
expected_output: []
- input: [1, 3, -2, 1]
expected_output: [2, 4, -1, 2]
*/
// </vc-description>

// <vc-spec>
fn incr_list(l: Vec<i32>) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        forall|i: int| 0 <= i < l.len() ==> l[i] + 1 <= i32::MAX,
    // pre-conditions-end

    // post-conditions-start
    ensures
        result.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> #[trigger] result[i] == l[i] + 1,
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    // impl-start
    let mut result = Vec::new();
    let mut i = 0;
    /* code modified by LLM (iteration 5): added proof block and precondition check for arithmetic overflow */
    while i < l.len()
        invariant
            i <= l.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == l[j] + 1,
        decreases l.len() - i,
    {
        /* code modified by LLM (iteration 5): added proof block to establish invariant preservation */
        proof {
            lemma_push_preserves_invariant(result, l, i, l[i] + 1);
        }
        result.push(l[i as usize] + 1);
        i += 1;
    }
    result
    // impl-end
}
// </vc-code>

}
fn main() {}