use vstd::prelude::*;

fn main() {
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
    assert(pushed.len() == vec.len() + 1);
    assert(pushed.index(l as int) == i);
    
    assert forall|k: int| 0 <= k < vec.len() implies vec[k] == pushed[k] by {
        assert(k < pushed.len() - 1);
    }
}

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            !(exists|j: int| 0 <= j < i && arr[j] == key),
    {
        if arr[i] == key {
            assert(exists|j: int| 0 <= j < arr.len() && arr[j] == key) by {
                assert(0 <= i < arr.len() && arr[i] == key);
            }
            return true;
        }
        i += 1;
    }
    
    assert(!(exists|j: int| 0 <= j < arr.len() && arr[j] == key)) by {
        assert(forall|j: int| 0 <= j < arr.len() ==> arr[j] != key);
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
    let mut i = 0;
    
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            forall|k: int|
                0 <= k < i ==> (!arr2@.contains(#[trigger] arr1[k]) ==> result@.contains(arr1[k])),
            forall|k: int, l: int|
                0 <= k < l < result.len() ==> #[trigger] result[k] != #[trigger] result[l],
    {
        if !contains(arr2, arr1[i]) && !contains(&result, arr1[i]) {
            result.push(arr1[i]);
            proof {
                lemma_vec_push(result@.drop_last(), arr1[i], result.len() - 1);
            }
        }
        i += 1;
    }
    
    let mut j = 0;
    while j < arr2.len()
        invariant
            0 <= j <= arr2.len(),
            forall|k: int|
                0 <= k < arr1.len() ==> (!arr2@.contains(#[trigger] arr1[k]) ==> result@.contains(arr1[k])),
            forall|k: int|
                0 <= k < j ==> (!arr1@.contains(#[trigger] arr2[k]) ==> result@.contains(arr2[k])),
            forall|k: int, l: int|
                0 <= k < l < result.len() ==> #[trigger] result[k] != #[trigger] result[l],
    {
        if !contains(arr1, arr2[j]) && !contains(&result, arr2[j]) {
            result.push(arr2[j]);
            proof {
                lemma_vec_push(result@.drop_last(), arr2[j], result.len() - 1);
            }
        }
        j += 1;
    }
    
    result
}

} // verus!