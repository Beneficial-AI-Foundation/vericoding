use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn contains(str: &Vec<i32>, key: i32) -> bool
{
    exists|i: int| 0 <= i < str.len() && (str[i] == key)
}

fn contains_exec(str: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> contains(str, key),
{
    let mut i = 0;
    while i < str.len()
        invariant
            forall|m: int| 0 <= m < i ==> (str[m] != key),
        decreases str.len() - i
    {
        if (str[i] == key) {
            return true;
        }
        i += 1;
    }
    false
}

proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: usize)
    requires
        l == vec.len(),
    ensures
        forall|k: int| 0 <= k < vec.len() ==> #[trigger] vec[k] == vec.push(i)[k],
        vec.push(i).index(l as int) == i,
{
}

spec fn contains_spec(arr: &Vec<i32>, elem: i32) -> bool {
    arr@.contains(elem)
}

proof fn lemma_contains_equivalence(arr: &Vec<i32>, elem: i32)
    ensures
        contains(arr, elem) <==> contains_spec(arr, elem)
{
}

proof fn lemma_result_contains_preservation(arr1: &Vec<i32>, result: &Vec<i32>, elem: i32)
    requires
        result@.contains(elem),
        forall|i: int| 0 <= i < result.len() ==> arr1@.contains(result[i])
    ensures
        arr1@.contains(elem)
{
}
// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

// <vc-spec>
fn remove_elements(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        forall|i: int|
            0 <= i < result.len() ==> (arr1@.contains(#[trigger] result[i]) && !arr2@.contains(
                #[trigger] result[i],
            )),
        forall|i: int|
            0 <= i < arr1.len() ==> (arr2@.contains(#[trigger] arr1[i]) || result@.contains(
                #[trigger] arr1[i],
            )),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 5): Added decreases clause to fix verification error */
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            forall|j: int| 0 <= j < result.len() ==> (arr1@.contains(#[trigger] result[j]) && !arr2@.contains(#[trigger] result[j])),
            forall|j: int| 0 <= j < i ==> (arr2@.contains(#[trigger] arr1[j]) || result@.contains(#[trigger] arr1[j])),
        decreases arr1.len() - i
    {
        /* code modified by LLM (iteration 4): Use exec function for runtime check */
        if !contains_exec(arr2, arr1[i]) {
            proof {
                lemma_contains_equivalence(arr2, arr1[i as int]);
                assert(!contains_spec(arr2, arr1[i as int]));
                assert(!arr2@.contains(arr1[i as int]));
            }
            result.push(arr1[i]);
            proof {
                lemma_vec_push(result@.drop_last(), arr1[i as int], (result.len() - 1) as usize);
            }
        }
        i += 1;
    }
    
    result
}
// </vc-code>

} // verus!

fn main() {}