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
    // The postconditions follow directly from the definition of push
    // First postcondition: all original elements remain in the same positions
    // Second postcondition: the new element is at position l
    // impl-end
}
// pure-end

fn contains(str: &Vec<i32>, key: i32) -> (result: bool)
    // post-conditions-start
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
    // post-conditions-end
{
    let mut idx = 0;
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while idx < str.len()
        invariant
            0 <= idx <= str.len(),
            forall|j: int| 0 <= j < idx ==> str[j] != key,
        decreases str.len() - idx,
    {
        if str[idx] == key {
            return true;
        }
        idx += 1;
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
    let mut idx = 0;
    
    while idx < arr1.len()
        invariant
            0 <= idx <= arr1.len(),
            forall|i: int|
                0 <= i < result.len() ==> (arr1@.contains(#[trigger] result[i]) && !arr2@.contains(
                    #[trigger] result[i],
                )),
            forall|i: int|
                0 <= i < idx ==> (arr2@.contains(#[trigger] arr1[i]) || result@.contains(
                    #[trigger] arr1[i],
                )),
        decreases arr1.len() - idx,
    {
        let elem = arr1[idx];
        if !contains(arr2, elem) {
            /* code modified by LLM (iteration 3): moved lemma call into same proof block to fix scope issue */
            proof {
                let old_result = result@;
                let old_len = result.len();
                lemma_vec_push(old_result, elem, old_len);
            }
            result.push(elem);
        }
        idx += 1;
    }
    
    result
}

} // verus!

fn main() {}