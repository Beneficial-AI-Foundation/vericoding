// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added decreases clauses to loops */
fn is_in(x: i32, arr: &Vec<i32>) -> (found: bool)
    ensures
        found == arr@.contains(x),
{
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|j: int| 0 <= j < i ==> arr@[j] != x,
        decreases arr.len() - i,
    {
        if arr[i] == x {
            return true;
        }
        i += 1;
    }
    false
}

spec fn seq_count<T>(s: Seq<T>, x: T) -> nat
    where T: core::cmp::Eq
{
    if s.len() == 0 {
        0
    } else if s[0] == x {
        1 + seq_count(s.subrange(1, s.len() as int), x)
    } else {
        seq_count(s.subrange(1, s.len() as int), x)
    }
}

fn no_duplicates_lemma(arr: &Vec<i32>)
    requires
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> #[trigger] arr[i] != #[trigger] arr[j],
    ensures
        forall|x: i32| seq_count(arr@, x) <= 1,
{
    assert forall|x: i32| seq_count(arr@, x) <= 1 by {
        if seq_count(arr@, x) > 1 {
            let i1 = choose|i: int| 0 <= i < arr.len() && arr@[i] == x;
            let i2 = choose|j: int| 0 <= j < arr.len() && j != i1 && arr@[j] == x;
            if i1 < i2 {
                assert(arr@[i1] == x && arr@[i2] == x);
                assert(arr[i1] != arr[i2]);
            } else {
                assert(arr@[i2] == x && arr@[i1] == x);
                assert(arr[i2] != arr[i1]);
            }
        }
    };
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
/* code modified by LLM (iteration 5): Added decreases clauses to loops */
{
    let mut result: Vec<i32> = Vec::new();
    
    let mut i: usize = 0;
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            forall|k: int| 0 <= k < i ==> (!arr2@.contains(arr1@[k]) ==> result@.contains(arr1@[k])),
            forall|k: int| 0 <= k < result.len() ==> (!arr1@.contains(result@[k]) || !arr2@.contains(result@[k])),
            forall|k: int, l: int| 0 <= k < l < result.len() ==> #[trigger] result[k] != #[trigger] result[l],
        decreases arr1.len() - i,
    {
        let elem = arr1[i];
        if !is_in(elem, arr2) {
            if !is_in(elem, &result) {
                result.push(elem);
            }
        }
        i += 1;
    }
    
    let mut j: usize = 0;
    while j < arr2.len()
        invariant
            0 <= j <= arr2.len(),
            forall|k: int| 0 <= k < j ==> (!arr1@.contains(arr2@[k]) ==> result@.contains(arr2@[k])),
            forall|k: int| 0 <= k < result.len() ==> (!arr1@.contains(result@[k]) || !arr2@.contains(result@[k])),
            forall|k: int, l: int| 0 <= k < l < result.len() ==> #[trigger] result[k] != #[trigger] result[l],
        decreases arr2.len() - j,
    {
        let elem = arr2[j];
        if !is_in(elem, arr1) {
            if !is_in(elem, &result) {
                result.push(elem);
            }
        }
        j += 1;
    }
    
    no_duplicates_lemma(&result);
    result
}
// </vc-code>

}
fn main() {}