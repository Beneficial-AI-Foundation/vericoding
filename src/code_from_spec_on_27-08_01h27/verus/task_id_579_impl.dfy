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
{
    let mut index = 0;
    while index < arr.len()
        invariant
            forall|m: int| 0 <= m < index ==> (arr[m] != key),
        decreases arr.len() - index,
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

spec fn seq_contains_value<T>(s: Seq<T>, val: T) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == val
}

proof fn lemma_push_preserves_contains(result: Seq<i32>, val: i32)
    ensures
        forall|x: i32| result.contains(x) ==> result.push(val).contains(x),
        result.push(val).contains(val),
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
    let mut result: Vec<i32> = Vec::new();
    
    let mut i = 0;
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            forall|k: int| 0 <= k < i ==> (!arr2@.contains(arr1[k]) ==> result@.contains(arr1[k])),
            forall|k: int, j: int| 0 <= k < j < result.len() ==> result[k] != result[j],
        decreases arr1.len() - i,
    {
        if !contains_exec(arr2, arr1[i]) && !contains_exec(&result, arr1[i]) {
            proof {
                lemma_push_preserves_contains(result@, arr1[i] as i32);
            }
            result.push(arr1[i]);
        }
        i += 1;
    }
    
    let mut j = 0;
    while j < arr2.len()
        invariant
            0 <= j <= arr2.len(),
            forall|k: int| 0 <= k < arr1.len() ==> (!arr2@.contains(arr1[k]) ==> result@.contains(arr1[k])),
            forall|k: int| 0 <= k < j ==> (!arr1@.contains(arr2[k]) ==> result@.contains(arr2[k])),
            forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] != result[l],
        decreases arr2.len() - j,
    {
        if !contains_exec(arr1, arr2[j]) && !contains_exec(&result, arr2[j]) {
            proof {
                lemma_push_preserves_contains(result@, arr2[j] as i32);
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