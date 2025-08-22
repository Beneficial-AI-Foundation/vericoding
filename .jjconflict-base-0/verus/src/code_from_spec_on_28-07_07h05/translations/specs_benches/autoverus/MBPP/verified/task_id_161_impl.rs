use vstd::prelude::*;

fn main() {
    // Empty main function
}

verus! {

proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: usize)
    requires
        l == vec.len(),
    ensures
        forall|k: int| 0 <= k < vec.len() ==> #[trigger] vec[k] == vec.push(i)[k],
        vec.push(i).index(l as int) == i,
{
    // The lemma holds by the definition of push operation
    // push appends the element at the end, so all previous indices remain unchanged
    // and the new element is at position l (which equals vec.len())
}

fn contains(str: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut idx = 0;
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while idx < str.len()
        invariant
            0 <= idx <= str.len(),
            forall|i: int| 0 <= i < idx ==> str[i] != key,
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
    ensures
        forall|i: int|
            0 <= i < result.len() ==> (arr1@.contains(#[trigger] result[i]) && !arr2@.contains(
                #[trigger] result[i],
            )),
        forall|i: int|
            0 <= i < arr1.len() ==> (arr2@.contains(#[trigger] arr1[i]) || result@.contains(
                #[trigger] arr1[i],
            )),
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 4): fixed loop invariant and assertions */
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
        let elem = arr1[i];
        /* code modified by LLM (iteration 4): restructured to ensure invariant maintenance */
        let elem_in_arr2 = contains(arr2, elem);
        if !elem_in_arr2 {
            /* code modified by LLM (iteration 4): added assertions before push to establish properties */
            assert(arr1@.contains(elem));
            assert(!arr2@.contains(elem));
            result.push(elem);
            /* code modified by LLM (iteration 4): assert after push that result contains elem */
            assert(result@.contains(elem));
        } else {
            /* code modified by LLM (iteration 4): elem is in arr2, so condition is satisfied */
            assert(arr2@.contains(elem));
        }
        i += 1;
        
        /* code modified by LLM (iteration 4): help verify invariant for next iteration */
        assert(forall|j: int|
            0 <= j < i ==> (arr2@.contains(arr1[j]) || result@.contains(arr1[j])));
    }
    
    result
}

} // verus!