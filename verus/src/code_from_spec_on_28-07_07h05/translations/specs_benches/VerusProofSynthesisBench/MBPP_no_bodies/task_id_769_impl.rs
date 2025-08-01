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
    // No additional proof steps needed as Verus can verify this automatically
    // impl-end
}
// pure-end

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    // post-conditions-start
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
    // post-conditions-end
{
    let mut idx = 0;
    /* code modified by LLM (iteration 1): added decreases clause to fix termination error */
    while idx < arr.len()
        invariant
            forall|i: int| 0 <= i < idx ==> arr[i] != key,
        decreases arr.len() - idx,
    {
        if arr[idx] == key {
            return true;
        }
        idx += 1;
    }
    false
}

fn difference(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        forall|i: int|
            0 <= i < arr1.len() ==> (!arr2@.contains(#[trigger] arr1[i]) ==> result@.contains(
                arr1[i],
            )),
        forall|i: int|
            0 <= i < arr2.len() ==> (!arr1@.contains(#[trigger] arr2[i]) ==> result@.contains(
                arr2[i],
            )),
        forall|i: int, j: int|
            0 <= i < j < result.len() ==> #[trigger] result[i] != #[trigger] result[j],
    // post-conditions-end
{
    let mut result = Vec::new();
    
    // Add elements from arr1 that are not in arr2
    let mut i = 0;
    /* code modified by LLM (iteration 4): fixed invariants to correctly state what elements have been processed and added */
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            forall|k: int| 0 <= k < i ==> (!arr2@.contains(arr1[k]) ==> result@.contains(arr1[k])),
            forall|k: int| 0 <= k < result.len() ==> (!arr2@.contains(result[k])),
            forall|k: int, j: int| 0 <= k < j < result.len() ==> result[k] != result[j],
        decreases arr1.len() - i,
    {
        if !contains(arr2, arr1[i]) && !contains(&result, arr1[i]) {
            result.push(arr1[i]);
        }
        i += 1;
    }
    
    // Add elements from arr2 that are not in arr1
    let mut j = 0;
    /* code modified by LLM (iteration 4): fixed invariants to properly maintain the properties from first loop and second loop */
    while j < arr2.len()
        invariant
            0 <= j <= arr2.len(),
            i == arr1.len(),
            forall|k: int| 0 <= k < arr1.len() ==> (!arr2@.contains(arr1[k]) ==> result@.contains(arr1[k])),
            forall|k: int| 0 <= k < j ==> (!arr1@.contains(arr2[k]) ==> result@.contains(arr2[k])),
            forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] != result[l],
        decreases arr2.len() - j,
    {
        if !contains(arr1, arr2[j]) && !contains(&result, arr2[j]) {
            result.push(arr2[j]);
        }
        j += 1;
    }
    
    result
}

} // verus!
fn main() {}