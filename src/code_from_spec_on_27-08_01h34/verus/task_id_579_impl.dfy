use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn contains(arr: &Vec<i32>, key: i32) -> bool {
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

proof fn lemma_contains_push(v: Seq<i32>, elem: i32)
    ensures
        v.push(elem).contains(elem),
        forall|x: i32| #[trigger] v.contains(x) ==> v.push(elem).contains(x),
{
    assert(v.push(elem)[v.len() as int] == elem);
    assert(v.push(elem).contains(elem));
    
    assert forall|x: i32| v.contains(x) ==> v.push(elem).contains(x) by {
        if v.contains(x) {
            let i = choose|i: int| 0 <= i < v.len() && v[i] == x;
            assert(v.push(elem)[i] == x);
            assert(v.push(elem).contains(x));
        }
    }
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
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            forall|k: int| 0 <= k < i ==> (!contains(arr2, arr1[k]) ==> result@.contains(arr1[k])),
            forall|j: int, k: int| 0 <= j < k < result.len() ==> result[j] != result[k],
        decreases
            arr1.len() - i,
    {
        if !contains_exec(arr2, arr1[i]) && !contains_exec(&result, arr1[i]) {
            proof {
                lemma_contains_push(result@, arr1[i]);
            }
            result.push(arr1[i]);
        }
        i += 1;
    }
    
    let mut j = 0;
    while j < arr2.len()
        invariant
            0 <= j <= arr2.len(),
            forall|k: int| 0 <= k < arr1.len() ==> (!contains(arr2, arr1[k]) ==> result@.contains(arr1[k])),
            forall|k: int| 0 <= k < j ==> (!contains(arr1, arr2[k]) ==> result@.contains(arr2[k])),
            forall|m: int, n: int| 0 <= m < n < result.len() ==> result[m] != result[n],
        decreases
            arr2.len() - j,
    {
        if !contains_exec(arr1, arr2[j]) && !contains_exec(&result, arr2[j]) {
            proof {
                lemma_contains_push(result@, arr2[j]);
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