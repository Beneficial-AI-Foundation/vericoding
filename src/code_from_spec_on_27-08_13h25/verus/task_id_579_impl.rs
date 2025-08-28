use vstd::prelude::*;

verus! {

// <vc-helpers>
fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut index = 0;
    while index < arr.len()
        invariant
            forall|m: int| 0 <= m < index ==> (arr[m] != key),
        decreases
            arr.len() - index,
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

proof fn lemma_vec_contains_after_push(vec: Seq<i32>, x: i32, y: i32)
    requires
        !vec.contains(x),
    ensures
        vec.push(y).contains(x) ==> x == y,
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
            forall|k: int| 0 <= k < i ==> (!arr2@.contains(arr1@[k]) ==> result@.contains(arr1@[k])),
            forall|k: int, m: int| 0 <= k < m < result.len() ==> result@[k] != result@[m],
        decreases
            arr1.len() - i,
    {
        let val = arr1[i];
        if !contains(arr2, val) && !contains(&result, val) {
            result.push(val);
            proof {
                lemma_vec_push(result@.drop_last(), val, result.len() as usize - 1);
            }
        }
        i += 1;
    }
    
    i = 0;
    while i < arr2.len()
        invariant
            forall|k: int| 0 <= k < arr1.len() ==> (!arr2@.contains(arr1@[k]) ==> result@.contains(arr1@[k])),
            forall|k: int| 0 <= k < i ==> (!arr1@.contains(arr2@[k]) ==> result@.contains(arr2@[k])),
            forall|k: int, m: int| 0 <= k < m < result.len() ==> result@[k] != result@[m],
        decreases
            arr2.len() - i,
    {
        let val = arr2[i];
        if !contains(arr1, val) && !contains(&result, val) {
            result.push(val);
            proof {
                lemma_vec_push(result@.drop_last(), val, result.len() as usize - 1);
            }
        }
        i += 1;
    }
    
    result
}
// </vc-code>

} // verus!

fn main() {}