use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn contains_spec(arr: &Vec<i32>, key: i32) -> bool {
    arr@.contains(key)
}

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
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

proof fn lemma_contains_push(vec: Seq<i32>, item: i32, x: i32)
    ensures
        vec.push(item).contains(x) == (vec.contains(x) || x == item)
{
    if vec.contains(x) {
        assert(vec.push(item).contains(x));
    } else if x == item {
        assert(vec.push(item).contains(x));
    } else {
        assert(!vec.push(item).contains(x));
    }
}

proof fn lemma_unique_preservation(vec: Seq<i32>, item: i32)
    requires
        forall|i: int, j: int| 0 <= i < j < vec.len() ==> #[trigger] vec[i] != #[trigger] vec[j],
        !vec.contains(item)
    ensures
        forall|i: int, j: int| 0 <= i < j < vec.push(item).len() ==> #[trigger] vec.push(item)[i] != #[trigger] vec.push(item)[j]
{
    let new_vec = vec.push(item);
    assert(forall|i: int, j: int| 0 <= i < j < vec.len() ==> vec[i] != vec[j]);
    assert(!vec.contains(item));
    assert(new_vec[vec.len() as int] == item);
}

proof fn lemma_contains_preserved_after_push(vec: Seq<i32>, item: i32, x: i32)
    requires
        vec.contains(x)
    ensures
        vec.push(item).contains(x)
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
    let mut result = Vec::<i32>::new();
    
    let mut i = 0;
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            forall|k: int| 0 <= k < i ==> (!arr2@.contains(#[trigger] arr1[k]) ==> result@.contains(arr1[k])),
            forall|k: int, j: int| 0 <= k < j < result.len() ==> #[trigger] result[k] != #[trigger] result[j]
        decreases arr1.len() - i
    {
        let elem = arr1[i];
        let contains_result = contains(arr2, elem);
        if !contains_result && !arr2@.contains(elem) {
            proof {
                lemma_unique_preservation(result@, elem);
            }
            result.push(elem);
        }
        proof {
            if !arr2@.contains(arr1[i as int]) {
                if arr2@.contains(elem) {
                    assert(result@.contains(arr1[i as int]));
                } else {
                    lemma_contains_preserved_after_push(result@, elem, arr1[i as int]);
                }
            }
        }
        i += 1;
    }
    
    let mut j = 0;
    while j < arr2.len()
        invariant
            0 <= j <= arr2.len(),
            forall|k: int| 0 <= k < arr1.len() ==> (!arr2@.contains(#[trigger] arr1[k]) ==> result@.contains(arr1[k])),
            forall|k: int| 0 <= k < j ==> (!arr1@.contains(#[trigger] arr2[k]) ==> result@.contains(arr2[k])),
            forall|k: int, l: int| 0 <= k < l < result.len() ==> #[trigger] result[k] != #[trigger] result[l]
        decreases arr2.len() - j
    {
        let elem = arr2[j];
        let contains_result = contains(arr1, elem);
        if !contains_result && !arr1@.contains(elem) {
            proof {
                lemma_unique_preservation(result@, elem);
            }
            result.push(elem);
        }
        proof {
            if !arr1@.contains(arr2[j as int]) {
                if arr1@.contains(elem) {
                    assert(result@.contains(arr2[j as int]));
                } else {
                    lemma_contains_preserved_after_push(result@, elem, arr2[j as int]);
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