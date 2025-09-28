// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn count_true_up_to(condition: &Vec<bool>, idx: int) -> nat
    decreases idx,
{
    if idx <= 0 {
        0nat
    } else if idx > condition.len() {
        count_true_up_to(condition, condition.len() as int)
    } else {
        count_true_up_to(condition, idx - 1) + if condition@[idx - 1] { 1nat } else { 0nat }
    }
}

/* helper modified by LLM (iteration 5): added decreases clause to recursive function */
proof fn lemma_count_true_monotonic(condition: &Vec<bool>, i: int, j: int)
    requires 0 <= i <= j <= condition.len(),
    ensures count_true_up_to(condition, i) <= count_true_up_to(condition, j),
    decreases j - i,
{
    if i < j {
        lemma_count_true_monotonic(condition, i, j - 1);
    }
}

proof fn lemma_count_true_bound(condition: &Vec<bool>, idx: int)
    requires 0 <= idx <= condition.len(),
    ensures count_true_up_to(condition, idx) <= idx,
    decreases idx,
{
    if idx > 0 {
        lemma_count_true_bound(condition, idx - 1);
    }
}
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
    /* code modified by LLM (iteration 5): added decreases clause to while loop */
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    
    while i < condition.len()
        invariant
            i <= condition.len(),
            result@.len() == count_true_up_to(condition, i as int),
            forall|k: int| 0 <= k < result@.len() ==> exists|j: int| 0 <= j < i && condition@[j] == true && result@[k] == arr@[j],
            forall|j: int| 0 <= j < i && condition@[j] == true ==> exists|k: int| 0 <= k < result@.len() && result@[k] == arr@[j],
        decreases condition.len() - i,
    {
        if condition[i] {
            result.push(arr[i]);
        }
        i += 1;
    }
    
    proof {
        assert(i == condition.len());
        assert(result@.len() == count_true_up_to(condition, condition.len() as int));
    }
    
    result
}
// </vc-code>


}
fn main() {}