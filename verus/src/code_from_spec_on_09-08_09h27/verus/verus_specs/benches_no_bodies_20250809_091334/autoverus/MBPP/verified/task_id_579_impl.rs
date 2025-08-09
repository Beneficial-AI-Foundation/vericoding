use vstd::prelude::*;

fn main() {
    let arr1 = vec![1, 2, 3, 4];
    let arr2 = vec![3, 4, 5, 6];
    let result = find_dissimilar(&arr1, &arr2);
    println!("Dissimilar elements: {:?}", result);
}

verus! {

proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: usize)
    requires
        l == vec.len(),
    ensures
        forall|k: int| 0 <= k < vec.len() ==> #[trigger] vec[k] == vec.push(i)[k],
        vec.push(i).index(l as int) == i,
{
    // The proof follows from the definition of push operation
    // All original elements remain at the same indices
    // The new element is added at the end (index l)
}

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut i = 0;
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while i < arr.len()
        invariant
            forall|j: int| 0 <= j < i ==> arr[j] != key,
        decreases arr.len() - i,
    {
        if arr[i] == key {
            return true;
        }
        i += 1;
    }
    false
}

fn find_dissimilar(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
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
{
    let mut result = Vec::new();
    
    // Add elements from arr1 that are not in arr2
    let mut i = 0;
    while i < arr1.len()
        invariant
            forall|k: int|
                0 <= k < i ==> (!arr2@.contains(arr1[k]) ==> result@.contains(arr1[k])),
            forall|x: int, y: int|
                0 <= x < y < result.len() ==> result[x] != result[y],
        decreases arr1.len() - i,
    {
        if !contains(arr2, arr1[i]) && !contains(&result, arr1[i]) {
            result.push(arr1[i]);
        }
        i += 1;
    }
    
    // Add elements from arr2 that are not in arr1
    let mut j = 0;
    while j < arr2.len()
        invariant
            forall|k: int|
                0 <= k < arr1.len() ==> (!arr2@.contains(arr1[k]) ==> result@.contains(arr1[k])),
            forall|k: int|
                0 <= k < j ==> (!arr1@.contains(arr2[k]) ==> result@.contains(arr2[k])),
            forall|x: int, y: int|
                0 <= x < y < result.len() ==> result[x] != result[y],
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