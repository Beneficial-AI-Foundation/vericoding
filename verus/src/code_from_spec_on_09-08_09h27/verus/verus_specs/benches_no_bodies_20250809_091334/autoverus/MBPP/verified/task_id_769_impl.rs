use vstd::prelude::*;

fn main() {
    let arr1 = vec![1, 2, 3, 4];
    let arr2 = vec![3, 4, 5, 6];
    let diff = difference(&arr1, &arr2);
    println!("Difference: {:?}", diff);
}

verus! {

proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: usize)
    requires
        l == vec.len(),
    ensures
        forall|k: int| 0 <= k < vec.len() ==> #[trigger] vec[k] == vec.push(i)[k],
        vec.push(i).index(l as int) == i,
{
    let pushed = vec.push(i);
    assert forall|k: int| 0 <= k < vec.len() implies #[trigger] vec[k] == pushed[k] by {
        assert(pushed[k] == vec[k]);
    }
    assert(pushed.index(l as int) == i);
}

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    for i in 0..arr.len()
        invariant
            forall|j: int| 0 <= j < i ==> arr[j] != key,
    {
        if arr[i] == key {
            assert(exists|j: int| 0 <= j < arr.len() && arr[j] == key) by {
                assert(0 <= i < arr.len() && arr[i as int] == key);
            }
            return true;
        }
    }
    assert(forall|j: int| 0 <= j < arr.len() ==> arr[j] != key);
    false
}

fn difference(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
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
    for i in 0..arr1.len()
        invariant
            forall|k: int| 0 <= k < i ==> (!arr2@.contains(arr1[k]) ==> result@.contains(arr1[k])),
            forall|p: int, q: int| 0 <= p < q < result.len() ==> result[p] != result[q],
    {
        if !contains(arr2, arr1[i]) && !contains(&result, arr1[i]) {
            result.push(arr1[i]);
        }
    }
    
    // Add elements from arr2 that are not in arr1
    for i in 0..arr2.len()
        invariant
            forall|k: int| 0 <= k < arr1.len() ==> (!arr2@.contains(arr1[k]) ==> result@.contains(arr1[k])),
            forall|k: int| 0 <= k < i ==> (!arr1@.contains(arr2[k]) ==> result@.contains(arr2[k])),
            forall|p: int, q: int| 0 <= p < q < result.len() ==> result[p] != result[q],
    {
        if !contains(arr1, arr2[i]) && !contains(&result, arr2[i]) {
            result.push(arr2[i]);
        }
    }
    
    result
}

} // verus!