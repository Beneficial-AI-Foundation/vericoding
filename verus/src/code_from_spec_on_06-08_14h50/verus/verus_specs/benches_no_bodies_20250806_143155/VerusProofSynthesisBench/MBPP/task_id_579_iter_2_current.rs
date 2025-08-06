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
    // The proof is automatic - Verus can prove these properties about sequence push
    // impl-end
}
// pure-end

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    // post-conditions-start
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
    // post-conditions-end
{
    let mut i = 0;
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while i < arr.len()
        invariant
            forall|j: int| 0 <= j < i ==> arr[j] != key,
        decreases arr.len() - i
    {
        if arr[i] == key {
            return true;
        }
        i += 1;
    }
    false
}

fn find_dissimilar(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
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
    let mut i1 = 0;
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while i1 < arr1.len()
        invariant
            forall|k: int| 0 <= k < i1 ==> (!arr2@.contains(arr1[k]) ==> result@.contains(arr1[k])),
            forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
        decreases arr1.len() - i1
    {
        if !contains(arr2, arr1[i1]) && !contains(&result, arr1[i1]) {
            result.push(arr1[i1]);
        }
        i1 += 1;
    }
    
    // Add elements from arr2 that are not in arr1
    let mut i2 = 0;
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while i2 < arr2.len()
        invariant
            forall|k: int| 0 <= k < arr1.len() ==> (!arr2@.contains(arr1[k]) ==> result@.contains(arr1[k])),
            forall|k: int| 0 <= k < i2 ==> (!arr1@.contains(arr2[k]) ==> result@.contains(arr2[k])),
            forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
        decreases arr2.len() - i2
    {
        if !contains(arr1, arr2[i2]) && !contains(&result, arr2[i2]) {
            result.push(arr2[i2]);
        }
        i2 += 1;
    }
    
    result
}

} // verus!

fn main() {}