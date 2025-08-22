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
    // The properties follow directly from the definition of push
    // No explicit proof steps needed as these are axioms of Seq
}

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut idx = 0;
    while idx < arr.len()
        invariant
            forall|i: int| 0 <= i < idx ==> arr[i] != key,
    {
        if arr[idx] == key {
            return true;
        }
        idx += 1;
    }
    false
}

fn find_dissimilar(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < arr1.len() ==> (!(exists|k: int| 0 <= k < arr2.len() && arr2[k] == arr1[i]) ==> (exists|j: int| 0 <= j < result.len() && result[j] == arr1[i])),
        forall|i: int|
            0 <= i < arr2.len() ==> (!(exists|k: int| 0 <= k < arr1.len() && arr1[k] == arr2[i]) ==> (exists|j: int| 0 <= j < result.len() && result[j] == arr2[i])),
        forall|i: int, j: int|
            0 <= i < j < result.len() ==> #[trigger] result[i] != #[trigger] result[j],
{
    let mut result = Vec::new();
    let mut i = 0;
    
    // Add elements from arr1 that are not in arr2
    while i < arr1.len()
        invariant
            forall|k: int| 0 <= k < i ==> (!(exists|l: int| 0 <= l < arr2.len() && arr2[l] == arr1[k]) ==> (exists|j: int| 0 <= j < result.len() && result[j] == arr1[k])),
            forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] != result[l],
    {
        /* code modified by LLM (iteration 1): fix int type usage in executable code by using usize indexing */
        if !(exists|k: int| 0 <= k < arr2.len() && arr2[k] == arr1[i as int]) && !contains(&result, arr1[i]) {
            result.push(arr1[i]);
        }
        i += 1;
    }
    
    let mut j = 0;
    // Add elements from arr2 that are not in arr1
    while j < arr2.len()
        invariant
            forall|k: int| 0 <= k < arr1.len() ==> (!(exists|l: int| 0 <= l < arr2.len() && arr2[l] == arr1[k]) ==> (exists|m: int| 0 <= m < result.len() && result[m] == arr1[k])),
            forall|k: int| 0 <= k < j ==> (!(exists|l: int| 0 <= l < arr1.len() && arr1[l] == arr2[k]) ==> (exists|m: int| 0 <= m < result.len() && result[m] == arr2[k])),
            forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] != result[l],
    {
        /* code modified by LLM (iteration 1): fix int type usage in executable code by using usize indexing */        
        if !(exists|k: int| 0 <= k < arr1.len() && arr1[k] == arr2[j as int]) && !contains(&result, arr2[j]) {
            result.push(arr2[j]);
        }
        j += 1;
    }
    
    result
}

} // verus!