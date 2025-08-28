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
            forall|k: int| 0 <= k < i ==> (!contains(arr2, arr1[k]) ==> result@.contains(arr1[k])),
            forall|k: int, m: int| 0 <= k < m < result.len() ==> result[k] != result[m],
    {
        let val = arr1[i];
        proof {
            let result_seq = result@;
            assert(forall|k: int| 0 <= k < result_seq.len() ==> result_seq.contains(result_seq[k]));
        }
        if !contains(arr2, val) {
            let mut found = false;
            let mut j = 0;
            while j < result.len()
                invariant
                    !found ==> forall|k: int| 0 <= k < j ==> result[k] != val,
            {
                if result[j] == val {
                    found = true;
                }
                j += 1;
            }
            if !found {
                result.push(val);
            }
        }
        i += 1;
    }
    
    i = 0;
    while i < arr2.len()
        invariant
            forall|k: int| 0 <= k < arr1.len() ==> (!contains(arr2, arr1[k]) ==> result@.contains(arr1[k])),
            forall|k: int| 0 <= k < i ==> (!contains(arr1, arr2[k]) ==> result@.contains(arr2[k])),
            forall|k: int, m: int| 0 <= k < m < result.len() ==> result[k] != result[m],
    {
        let val = arr2[i];
        proof {
            let result_seq = result@;
            assert(forall|k: int| 0 <= k < result_seq.len() ==> result_seq.contains(result_seq[k]));
        }
        if !contains(arr1, val) {
            let mut found = false;
            let mut j = 0;
            while j < result.len()
                invariant
                    !found ==> forall|k: int| 0 <= k < j ==> result[k] != val,
            {
                if result[j] == val {
                    found = true;
                }
                j += 1;
            }
            if !found {
                result.push(val);
            }
        }
        i += 1;
    }
    
    result
}
// </vc-code>

} // verus!

fn main() {}