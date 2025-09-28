// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The `builtin` module is not directly accessible in Verus, causing a compilation error. Changed `builtin::Eq` to `vstd::pervasive::Eq` and removed `core::marker::Copy` as it's not needed for the `contains` lemma to compile. */
fn min_i8(a: i8, b: i8) -> i8 { if a < b { a } else { b } }

pub fn max_i8(a: i8, b: i8) -> i8 { if a > b { a } else { b } }

proof fn lemma_vec_to_seq_contains<T: vstd::pervasive::Eq>(v: &Vec<T>, value: T)
    ensures
        v@.contains(value) == v.contains(&value),
{
    // This lemma is needed because `v@.contains` isn't directly linked to `v.contains`
    // for external vectors. For internal usage, they might be synonyms depending on context.
    // Here, we're reasoning about the mathematical sequence property.
    // Since the original problem is about `Vec<i8>`, this lemma helps bridge the gap.
}
// </vc-helpers>

// <vc-spec>
fn union1d(ar1: Vec<i8>, ar2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        /* Union property: every element from either input array is in result */
        forall|i: int| 0 <= i < ar1.len() ==> 
            #[trigger] result@.contains(ar1[i]),
        forall|i: int| 0 <= i < ar2.len() ==> 
            #[trigger] result@.contains(ar2[i]),
        /* Completeness: every element in result comes from one of the input arrays */
        forall|j: int| 0 <= j < result.len() ==> 
            ar1@.contains(result[j]) || ar2@.contains(result[j]),
        /* Sorted property: result is sorted in ascending order */
        forall|i: int, j: int| 0 <= i < j < result.len() ==> 
            #[trigger] result[i] <= #[trigger] result[j],
        /* Uniqueness property: no duplicate elements */
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && i != j ==> 
            #[trigger] result[i] != #[trigger] result[j],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Removed pure keyword from `min_i8` and `max_i8` calls as they are not pure functions. */
{
    let mut result_vec: Vec<i8> = Vec::new();
    let mut i: int = 0;
    let mut j: int = 0;

    while i < ar1.len() || j < ar2.len()
        invariant
            0 <= i <= ar1.len(),
            0 <= j <= ar2.len(),
            result_vec.len() >= 0,
            forall|k: int| 0 <= k < result_vec.len() ==> 
                ar1@.contains(result_vec@[k]) || ar2@.contains(result_vec@[k]),
            forall|a: int, b: int| 0 <= a < b < result_vec.len() ==> 
                result_vec@[a] < result_vec@[b],
            forall|a: int, b: int| 0 <= a < result_vec.len() && 0 <= b < result_vec.len() && a != b ==> 
                result_vec@[a] != result_vec@[b],
            forall|k: int| 0 <= k < result_vec.len() ==> 
                (exists|idx: int| 0 <= idx < ar1.len() && ar1@[idx] == result_vec@[k] && ar1@[idx] <= ar1@[i.min(ar1.len())]) ||
                (exists|idx: int| 0 <= idx < ar2.len() && ar2@[idx] == result_vec@[k] && ar2@[idx] <= ar2@[j.min(ar2.len())]),
            result_vec.len() == 0 ||
            ((i < ar1.len() && j < ar2.len() ==> result_vec@.last().get_Some_0() < ar1@[i] || result_vec@.last().get_Some_0() < ar2@[j])) &&
            ((i >= ar1.len() && j < ar2.len() ==> result_vec@.last().get_Some_0() < ar2@[j])) &&
            ((i < ar1.len() && j >= ar2.len() ==> result_vec@.last().get_Some_0() < ar1@[i])),

        decreases (ar1.len() - i) + (ar2.len() - j)
    {
        let val1 = if i < ar1.len() { Some(ar1[i as usize]) } else { None };
        let val2 = if j < ar2.len() { Some(ar2[j as usize]) } else { None };

        let mut next_val: Option<i8> = None;

        if let Some(v1) = val1 {
            if let Some(v2) = val2 {
                if v1 < v2 {
                    next_val = Some(v1);
                    i = i + 1;
                } else if v2 < v1 {
                    next_val = Some(v2);
                    j = j + 1;
                } else { // v1 == v2
                    next_val = Some(v1);
                    i = i + 1;
                    j = j + 1;
                }
            } else { // val1 is Some, val2 is None
                next_val = Some(v1);
                i = i + 1;
            }
        } else { // val1 is None
            if let Some(v2) = val2 {
                next_val = Some(v2);
                j = j + 1;
            } else { // Both are None, loop should terminate
                // This branch shouldn't be reached as the loop condition handles it.
            }
        }

        if let Some(nv) = next_val {
            let mut should_add = true;
            if result_vec.len() > 0 {
                if result_vec.last().get_Some_0() == nv {
                    should_add = false;
                }
            }

            if should_add {
                result_vec.push(nv);
            }
        }
    }

    result_vec
}
// </vc-code>


}
fn main() {}