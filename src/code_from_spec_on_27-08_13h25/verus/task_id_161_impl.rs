use vstd::prelude::*;

verus! {

// <vc-helpers>
fn contains(str: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < str.len() && (str@[i] == key)),
{
    let mut i = 0;
    while i < str.len()
        invariant
            forall|m: int| 0 <= m < i ==> (str@[m] != key),
    {
        if (str@[i] == key) {
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
            forall|k: int| 0 <= k < result.len() ==> (arr1@.contains(#[trigger] result@[k]) && !arr2@.contains(#[trigger] result@[k])),
            forall|k: int| 0 <= k < i ==> (arr2@.contains(#[trigger] arr1@[k]) || result@.contains(#[trigger] arr1@[k])),
    {
        let mut found_in_arr2 = false;
        let mut j = 0;
        while j < arr2.len()
            invariant
                0 <= j <= arr2.len(),
                !found_in_arr2 ==> forall|k: int| 0 <= k < j ==> arr2@[k] != arr1@[i],
        {
            if arr2@[j] == arr1@[i] {
                found_in_arr2 = true;
                break;
            }
            j += 1;
        }
        
        let mut found_in_result = false;
        let mut k = 0;
        while k < result.len()
            invariant
                0 <= k <= result.len(),
                !found_in_result ==> forall|m: int| 0 <= m < k ==> result@[m] != arr1@[i],
        {
            if result@[k] == arr1@[i] {
                found_in_result = true;
                break;
            }
            k += 1;
        }

        if !found_in_arr2 && !found_in_result {
            result.push(arr1@[i]);
        }
        i += 1;
    }
    result
}
// </vc-code>

} // verus!

fn main() {}