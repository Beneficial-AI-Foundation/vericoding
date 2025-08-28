use vstd::prelude::*;

verus! {

// <vc-helpers>
fn contains(str: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str[i] == key)),
{
    let mut i = 0;
    while i < str.len()
        invariant
            forall|m: int| 0 <= m < i ==> (str[m] != key),
        decreases
            str.len() - i,
    {
        if (str[i] == key) {
            return true;
        }
        i += 1;
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
// </vc-helpers>

// <vc-spec>
fn remove_elements(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        forall|i: int|
            0 <= i < result.len() ==> (arr1@.contains(#[trigger] result[i]) && !arr2@.contains(
                #[trigger] result[i],
            )),
        forall|i: int|
            0 <= i < arr1.len() ==> (arr2@.contains(#[trigger] arr1[i]) || result@.contains(
                #[trigger] arr1[i],
            )),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < arr1.len()
        invariant
            forall|k: int| 0 <= k < result.len() ==> (arr1@.contains(#[trigger] result[k]) && !arr2@.contains(#[trigger] result[k])),
            forall|k: int| 0 <= k < i ==> (arr2@.contains(#[trigger] arr1[k]) || result@.contains(#[trigger] arr1[k])),
        decreases
            arr1.len() - i,
    {
        let elem = arr1[i];
        let mut arr2_contains = false;
        let mut result_contains = false;
        let mut j = 0;
        while j < arr2.len()
            invariant
                0 <= j <= arr2.len(),
                arr2_contains ==> (exists|k: int| 0 <= k < j && arr2[k] == elem),
                !arr2_contains ==> (forall|k: int| 0 <= k < j ==> arr2[k] != elem),
            decreases
                arr2.len() - j,
        {
            if arr2[j] == elem {
                arr2_contains = true;
                break;
            }
            j += 1;
        }
        if !arr2_contains {
            j = 0;
            while j < result.len()
                invariant
                    0 <= j <= result.len(),
                    result_contains ==> (exists|k: int| 0 <= k < j && result[k] == elem),
                    !result_contains ==> (forall|k: int| 0 <= k < j ==> result[k] != elem),
                decreases
                    result.len() - j,
            {
                if result[j] == elem {
                    result_contains = true;
                    break;
                }
                j += 1;
            }
        }
        if !arr2_contains && !result_contains {
            proof {
                lemma_vec_push(result@, elem, result.len());
            }
            result.push(elem);
        }
        i += 1;
    }
    result
}
// </vc-code>

} // verus!

fn main() {}