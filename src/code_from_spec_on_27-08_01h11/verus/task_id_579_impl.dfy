use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn contains(arr: &Vec<i32>, key: i32) -> bool
{
    arr@.contains(key)
}

fn contains_exec(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == contains(arr, key),
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
        result == arr@.contains(key),
{
    let mut index = 0;
    while index < arr.len()
        invariant
            forall|m: int| 0 <= m < index ==> (arr[m] != key),
        decreases arr.len() - index
    {
        if (arr[index] == key) {
            return true;
        }
        index += 1;
    }
    false
}

proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: usize)
    requires
        l == vec.len(),
    ensures
        forall|k: int| 0 <= k < vec.len() ==> #[trigger] vec[k] == vec.push(i)[k],
        vec.push(i).index(l as int) == i,
{
}

proof fn lemma_unique_after_push(result: Seq<i32>, value: i32)
    requires
        !result.contains(value),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> #[trigger] result[i] != #[trigger] result[j],
    ensures
        forall|i: int, j: int| 0 <= i < j < result.push(value).len() ==> #[trigger] result.push(value)[i] != #[trigger] result.push(value)[j],
{
}

proof fn lemma_result_preserved_after_push(result_old: Seq<i32>, result_new: Seq<i32>, value: i32)
    requires
        result_new == result_old.push(value),
    ensures
        forall|x: i32| result_old.contains(x) ==> result_new.contains(x),
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
            forall|k: int| 0 <= k < i ==> (!arr2@.contains(#[trigger] arr1[k]) ==> result@.contains(arr1[k])),
            forall|k: int, l: int| 0 <= k < l < result.len() ==> #[trigger] result[k] != #[trigger] result[l],
        decreases arr1.len() - i
    {
        let val = arr1[i];
        if !contains_exec(arr2, val) && !contains_exec(&result, val) {
            proof {
                lemma_unique_after_push(result@, val);
            }
            result.push(val);
        }
        i += 1;
    }
    
    let mut j = 0;
    while j < arr2.len()
        invariant
            forall|k: int| 0 <= k < arr1.len() ==> (!arr2@.contains(#[trigger] arr1[k]) ==> result@.contains(arr1[k])),
            forall|k: int| 0 <= k < j ==> (!arr1@.contains(#[trigger] arr2[k]) ==> result@.contains(arr2[k])),
            forall|k: int, l: int| 0 <= k < l < result.len() ==> #[trigger] result[k] != #[trigger] result[l],
        decreases arr2.len() - j
    {
        let val = arr2[j];
        if !contains_exec(arr1, val) && !contains_exec(&result, val) {
            proof {
                let result_old = result@;
                lemma_unique_after_push(result@, val);
                lemma_result_preserved_after_push(result_old, result_old.push(val), val);
            }
            result.push(val);
        } else {
            proof {
                if !contains_exec(arr1, val) {
                    assert(contains_exec(&result, val));
                    assert(result@.contains(val));
                }
            }
        }
        j += 1;
    }
    
    result
}
// </vc-code>

} // verus!

fn main() {}