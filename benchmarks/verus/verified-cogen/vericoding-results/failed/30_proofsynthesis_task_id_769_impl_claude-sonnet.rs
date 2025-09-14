// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn contains_helper(v: &Vec<i32>, elem: i32) -> bool {
    v@.contains(elem)
}

proof fn lemma_distinct_preservation(result: &Vec<i32>, new_elem: i32)
    requires
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
        !result@.contains(new_elem),
    ensures
        forall|i: int, j: int| 0 <= i < j < result.len() + 1 ==> {
            let extended = result@.push(new_elem);
            extended[i] != extended[j]
        },
{
}

proof fn lemma_push_contains(v: &Vec<i32>, elem: i32, target: i32)
    ensures
        v@.push(elem).contains(target) <==> (v@.contains(target) || elem == target),
{
}
// </vc-helpers>

// <vc-spec>
fn difference(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)

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
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): used arr1[i] and arr2[j] instead of arr1@[i as int] and arr2@[j as int] to fix ghost type usage error */
    let mut result: Vec<i32> = Vec::new();
    
    let mut i = 0;
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            forall|k: int| 0 <= k < i ==> (!arr2@.contains(arr1@[k]) ==> result@.contains(arr1@[k])),
            forall|x: int, y: int| 0 <= x < y < result.len() ==> result@[x] != result@[y],
    {
        if !arr2@.contains(arr1[i]) && !result@.contains(arr1[i]) {
            proof {
                lemma_distinct_preservation(&result, arr1[i]);
            }
            result.push(arr1[i]);
        }
        i += 1;
    }
    
    let mut j = 0;
    while j < arr2.len()
        invariant
            0 <= j <= arr2.len(),
            forall|k: int| 0 <= k < arr1.len() ==> (!arr2@.contains(arr1@[k]) ==> result@.contains(arr1@[k])),
            forall|k: int| 0 <= k < j ==> (!arr1@.contains(arr2@[k]) ==> result@.contains(arr2@[k])),
            forall|x: int, y: int| 0 <= x < y < result.len() ==> result@[x] != result@[y],
    {
        if !arr1@.contains(arr2[j]) && !result@.contains(arr2[j]) {
            proof {
                lemma_distinct_preservation(&result, arr2[j]);
            }
            result.push(arr2[j]);
        }
        j += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}