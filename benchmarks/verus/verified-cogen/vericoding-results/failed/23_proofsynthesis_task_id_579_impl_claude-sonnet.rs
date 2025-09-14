// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed proof block from lemma since it's not a spec function with decreases */
spec fn is_unique_element(x: i32, arr1: &Seq<i32>, arr2: &Seq<i32>) -> bool {
    (!arr1.contains(x) && arr2.contains(x)) || (arr1.contains(x) && !arr2.contains(x))
}

fn vec_contains(v: &Vec<i32>, x: i32) -> (result: bool)
    ensures result == v@.contains(x)
{
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            !v@.subrange(0, i as int).contains(x),
        decreases v.len() - i
    {
        if v[i] == x {
            return true;
        }
        i += 1;
    }
    false
}

proof fn lemma_unique_preserves_distinctness(result: &Vec<i32>, x: i32, idx: usize)
    requires
        idx < result.len(),
        forall|i: int, j: int| 0 <= i < j < idx ==> #[trigger] result[i] != #[trigger] result[j],
        forall|k: int| 0 <= k < idx ==> #[trigger] result[k] != x,
    ensures
        forall|i: int, j: int| 0 <= i < j < idx + 1 ==> #[trigger] result[i] != #[trigger] result[j],
{
    assert(result[idx as int] == x);
    assert(forall|k: int| 0 <= k < idx ==> result[k] != x);
    assert(forall|i: int, j: int| 0 <= i < j < idx ==> result[i] != result[j]);
}
// </vc-helpers>

// <vc-spec>
fn find_dissimilar(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)

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
    /* code modified by LLM (iteration 5): removed proof blocks from code section to fix compilation error */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            forall|k: int| 0 <= k < i ==> (!arr2@.contains(#[trigger] arr1[k]) ==> result@.contains(arr1[k])),
            forall|p: int, q: int| 0 <= p < q < result.len() ==> #[trigger] result[p] != #[trigger] result[q],
        decreases arr1.len() - i
    {
        if !vec_contains(arr2, arr1[i]) && !vec_contains(&result, arr1[i]) {
            result.push(arr1[i]);
        }
        i += 1;
    }
    
    let mut j = 0;
    
    while j < arr2.len()
        invariant
            0 <= j <= arr2.len(),
            forall|k: int| 0 <= k < arr1.len() ==> (!arr2@.contains(#[trigger] arr1[k]) ==> result@.contains(arr1[k])),
            forall|k: int| 0 <= k < j ==> (!arr1@.contains(#[trigger] arr2[k]) ==> result@.contains(arr2[k])),
            forall|p: int, q: int| 0 <= p < q < result.len() ==> #[trigger] result[p] != #[trigger] result[q],
        decreases arr2.len() - j
    {
        if !vec_contains(arr1, arr2[j]) && !vec_contains(&result, arr2[j]) {
            result.push(arr2[j]);
        }
        j += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}