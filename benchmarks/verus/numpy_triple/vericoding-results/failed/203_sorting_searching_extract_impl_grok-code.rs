// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers needed as fixes are in the code section. */
// </vc-helpers>

// <vc-spec>
fn extract(condition: &Vec<bool>, arr: &Vec<i8>) -> (result: Vec<i8>)
    requires condition.len() == arr.len(),
    ensures
        /* Each element in result comes from arr at a position where condition is true */
        forall|k: int| 0 <= k < result@.len() ==>
            exists|i: int| 0 <= i < arr@.len() && condition@[i] == true && #[trigger] result@[k] == arr@[i],
        /* Every True position in condition contributes exactly one element to the result */
        forall|i: int| 0 <= i < condition@.len() && condition@[i] == true ==>
            exists|k: int| 0 <= k < result@.len() && #[trigger] result@[k] == arr@[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added invariant to track the count of true conditions seen, which helps Verus verify the exists clauses by linking the number of pushed elements to the number of true conditions processed. */
    let mut result = Vec::new();
    let mut i: usize = 0;
    let mut true_count: usize = 0;
    while i < condition.len()
        invariant
            i <= condition.len(),
            condition@.len() == arr@.len(),
            true_count == ({j: int | 0 <= j < i && condition@[j] == true}).len(),
            result@.len() == true_count,
            forall|k: int| 0 <= k < result@.len() ==>
                exists|j: int| 0 <= j < i && condition@[j] == true && #[trigger] result@[k] == arr@[j],
            forall|j: int| 0 <= j < i && condition@[j] == true ==>
                exists|k: int| 0 <= k < result@.len() && #[trigger] result@[k] == arr@[j],
        decreases condition.len() - i
    {
        if condition[i] {
            result.push(arr[i]);
            true_count += 1;
        }
        proof {
            // Manually assert the invariants hold after the operation for verification help
            assert(forall|k: int| 0 <= k < result@.len() ==>
                exists|j: int| 0 <= j < (i + 1) && condition@[j] == true && result@[k] == arr@[j]);
            assert(forall|j: int| 0 <= j < (i + 1) && condition@[j] == true ==>
                exists|k: int| 0 <= k < result@.len() && result@[k] == arr@[j]);
        }
        i += 1;
    }
    proof {
        // Assert the ensures at the end
        assert(forall|k: int| 0 <= k < result@.len() ==>
            exists|j: int| 0 <= j < arr@.len() && condition@[j] == true && result@[k] == arr@[j]);
        assert(forall|j: int| 0 <= j < condition@.len() && condition@[j] == true ==>
            exists|k: int| 0 <= k < result@.len() && result@[k] == arr@[j]);
    }
    result
}
// </vc-code>


}
fn main() {}