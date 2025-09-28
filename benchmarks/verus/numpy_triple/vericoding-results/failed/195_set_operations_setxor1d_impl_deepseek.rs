// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn contains_element(arr: Seq<i32>, elem: i32) -> bool {
    exists|i: int| 0 <= i < arr.len() && arr[i] == elem
}

spec fn is_sorted(arr: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
}

spec fn has_no_duplicates(arr: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() && i != j ==> arr[i] != arr[j]
}

spec fn in_exactly_one(ar1: Seq<i32>, ar2: Seq<i32>, elem: i32) -> bool {
    (contains_element(ar1, elem) && !contains_element(ar2, elem)) ||
    (contains_element(ar2, elem) && !contains_element(ar1, elem))
}
// </vc-preamble>

// <vc-helpers>

proof fn lemma_len_conversion(len: nat) 
    ensures 
        len as int == len,
{
}

// </vc-helpers>

// <vc-spec>
fn numpy_setxor1d(ar1: &Vec<i32>, ar2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        /* Result is sorted */
        is_sorted(result@),
        /* Result has no duplicates */
        has_no_duplicates(result@),
        /* Every element in result is from exactly one input array */
        forall|i: int| 0 <= i < result.len() ==> #[trigger] in_exactly_one(ar1@, ar2@, result[i]),
        /* Every element that appears in exactly one input array is in the result */
        forall|x: i32| in_exactly_one(ar1@, ar2@, x) ==> contains_element(result@, x)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): removed lemma_len_conversion calls and fixed compilation */
    let mut result = Vec::new();
    let mut i = 0;
    let mut j = 0;
    
    while i < ar1.len() && j < ar2.len()
        invariant
            is_sorted(Seq::new(result.len() as nat, |k: int| result@[k])),
            has_no_duplicates(Seq::new(result.len() as nat, |k: int| result@[k])),
            forall|k: int| 0 <= k < result.len() ==> in_exactly_one(ar1@, ar2@, result@[k]),
            forall|x: i32| in_exactly_one(ar1@, ar2@, x) && x <= ar1[i as int] && x <= ar2[j as int] ==> contains_element(result@, x),
            i <= ar1.len(),
            j <= ar2.len(),
            is_sorted(ar1@.subrange(i as int, ar1@.len() as int)),
            is_sorted(ar2@.subrange(j as int, ar2@.len() as int)),
        decreases
            (ar1.len() - i + ar2.len() - j) as nat
    {
        if ar1[i] < ar2[j] {
            result.push(ar1[i]);
            i += 1;
        } else if ar2[j] < ar1[i] {
            result.push(ar2[j]);
            j += 1;
        } else {
            i += 1;
            j += 1;
        }
    }
    
    while i < ar1.len()
        invariant
            is_sorted(Seq::new(result.len() as nat, |k: int| result@[k])),
            has_no_duplicates(Seq::new(result.len() as nat, |k: int| result@[k])),
            forall|k: int| 0 <= k < result.len() ==> in_exactly_one(ar1@, ar2@, result@[k]),
            forall|x: i32| in_exactly_one(ar1@, ar2@, x) && x <= ar1[i as int] ==> contains_element(result@, x),
            i <= ar1.len(),
            j == ar2.len(),
        decreases
            (ar1.len() - i) as nat
    {
        result.push(ar1[i]);
        i += 1;
    }
    
    while j < ar2.len()
        invariant
            is_sorted(Seq::new(result.len() as nat, |k: int| result@[k])),
            has_no_duplicates(Seq::new(result.len() as nat, |k: int| result@[k])),
            forall|k: int| 0 <= k < result.len() ==> in_exactly_one(ar1@, ar2@, result@[k]),
            forall|x: i32| in_exactly_one(ar1@, ar2@, x) && x <= ar2[j as int] ==> contains_element(result@, x),
            i == ar1.len(),
            j <= ar2.len(),
        decreases
            (ar2.len() - j) as nat
    {
        result.push(ar2[j]);
        j += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}