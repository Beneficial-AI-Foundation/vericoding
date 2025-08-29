use vstd::prelude::*;

verus! {

// <vc-helpers>
lemma lemma_precondition_implies_bound(arr1: &Vec<i32>, arr2: &Vec<i32>, i: usize)
    requires
        i < arr1.len(),
        arr1.len() == arr2.len(),
        forall|j: int| (0 <= j < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[j] - arr2[j]) <= i32::MAX),
    ensures
        i32::MIN <= arr1[i as int] - arr2[i as int] <= i32::MAX,
{
    assert(0 <= i as int < arr1.len());
}
// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

// <vc-spec>
fn element_wise_subtract(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        arr1.len() == arr2.len(),
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] - arr2[i]) <= i32::MAX),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result.len() == arr1.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] - arr2[i]),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    /* code modified by LLM (iteration 5): added lemma call to establish overflow bounds */
    while i < arr1.len()
        invariant
            i <= arr1.len(),
            arr1.len() == arr2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == #[trigger] (arr1[j] - arr2[j]),
            forall|j: int| (0 <= j < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[j] - arr2[j]) <= i32::MAX),
        decreases arr1.len() - i,
    {
        assert(i < arr1.len() && i < arr2.len());
        /* code modified by LLM (iteration 5): use lemma to prove bounds before assertion */
        lemma_precondition_implies_bound(arr1, arr2, i);
        assert(i32::MIN <= arr1[i as int] - arr2[i as int] <= i32::MAX);
        let diff = arr1[i] - arr2[i];
        result.push(diff);
        i += 1;
    }
    result
}
// </vc-code>

} // verus!

fn main() {}