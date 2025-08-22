use vstd::prelude::*;

verus! {

proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: usize)
    // pre-conditions-start
    requires
        l == vec.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|k: int| 0 <= k < vec.len() ==> #[trigger] vec[k] == vec.push(i)[k],
        vec.push(i).index(l as int) == i,
    // post-conditions-end
{
    // impl-start
    // The proof is automatic - Verus can prove these properties of push directly
    // impl-end
}
// pure-end

fn contains(str: &Vec<i32>, key: i32) -> (result: bool)
    // post-conditions-start
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
    // post-conditions-end
{
    let mut i = 0;
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while i < str.len()
        invariant
            0 <= i <= str.len(),
            forall|j: int| 0 <= j < i ==> str[j] != key,
        decreases str.len() - i,
    {
        if str[i] == key {
            return true;
        }
        i += 1;
    }
    false
}

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
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 3): updated loop invariant to properly handle the case after incrementing i */
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            forall|j: int|
                0 <= j < result.len() ==> (arr1@.contains(#[trigger] result[j]) && !arr2@.contains(
                    #[trigger] result[j],
                )),
            forall|j: int|
                0 <= j < i ==> (arr2@.contains(#[trigger] arr1[j]) || result@.contains(
                    #[trigger] arr1[j],
                )),
        decreases arr1.len() - i,
    {
        /* code modified by LLM (iteration 3): restructured loop body to ensure invariant is maintained */
        let current_element = arr1[i];
        if !contains(arr2, current_element) {
            result.push(current_element);
            /* code modified by LLM (iteration 4): wrapped lemma call in proof block to fix compilation error */
            proof {
                lemma_vec_push(result@, current_element, result.len() - 1);
            }
            /* code modified by LLM (iteration 3): assert that arr1 contains current element */
            assert(arr1@.contains(current_element));
            /* code modified by LLM (iteration 3): assert that arr2 does not contain current element */
            assert(!arr2@.contains(current_element));
        }
        i += 1;
    }
    
    result
}

} // verus!

fn main() {}