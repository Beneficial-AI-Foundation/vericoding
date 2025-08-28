use vstd::prelude::*;

verus! {

// <vc-helpers>
fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    // post-conditions-start
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
    // post-conditions-end
{
    // impl-start
    let mut index = 0;
    while index < arr.len()
        // invariants-start
        invariant
            forall|m: int| 0 <= m < index ==> (arr[m] != key),
        // invariants-end
    {
        if (arr[index] == key) {
            return true;
        }
        index += 1;
    }
    false
    // impl-end
}

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
    // impl-end
}

proof fn lemma_vec_unique_preserved(vec: &Vec<i32>, elem: i32)
    requires
        forall|i: int, j: int| 0 <= i < j < vec.len() ==> #[trigger] vec[i] != #[trigger] vec[j],
        !vec@.contains(elem),
    ensures
        forall|i: int, j: int| 0 <= i < j < (vec.len() + 1) ==> #[trigger] vec@.push(elem)[i] != #[trigger] vec@.push(elem)[j],
{
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    let mut result: Vec<i32> = vec![];
    
    let mut i = 0;
    while i < arr1.len()
        invariant
            forall|k: int| 0 <= k < i ==> (!arr2@.contains(arr1[k]) ==> result@.contains(arr1[k])),
            forall|k: int, j: int| 0 <= k < j < result.len() ==> #[trigger] result[k] != #[trigger] result[j],
    {
        if !contains(arr2, arr1[i]) && !contains(&result, arr1[i]) {
            proof {
                lemma_vec_unique_preserved(&result, arr1[i]);
            }
            result.push(arr1[i]);
        }
        i += 1;
    }
    
    let mut j = 0;
    while j < arr2.len()
        invariant
            forall|k: int| 0 <= k < arr1.len() ==> (!arr2@.contains(arr1[k]) ==> result@.contains(arr1[k])),
            forall|k: int| 0 <= k < j ==> (!arr1@.contains(arr2[k]) ==> result@.contains(arr2[k])),
            forall|k: int, l: int| 0 <= k < l < result.len() ==> #[trigger] result[k] != #[trigger] result[l],
    {
        if !contains(arr1, arr2[j]) && !contains(&result, arr2[j]) {
            proof {
                lemma_vec_unique_preserved(&result, arr2[j]);
            }
            result.push(arr2[j]);
        }
        j += 1;
    }
    
    result
}
// </vc-code>

} // verus!

fn main() {}