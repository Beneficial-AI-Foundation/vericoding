// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    /* code modified by LLM (iteration 5): replaced result.is_empty() with result.len() == 0 to fix compilation error */
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    while i < ar1.len() && j < ar2.len()
        invariant
            0 <= i <= ar1.len(),
            0 <= j <= ar2.len(),
            forall|k: int| (0 <= k < i && i > 0) ==> ar1@[k] <= ar1@[i-1],
            forall|k: int| (0 <= k < j && j > 0) ==> ar2@[k] <= ar2@[j-1],
            forall|m: int| 0 <= m < result.len() ==> 
                exists|n: int| 0 <= n < i && ar1@[n] == result@[m] || 
                exists|p: int| 0 <= p < j && ar2@[p] == result@[m],
            forall|m: int, l: int| 0 <= m < l < result.len() ==> result@[m] <= result@[l],
            forall|m: int, l: int| 0 <= m < l < result.len() ==> result@[m] != result@[l],
    {
        let a_item = ar1[i];
        let b_item = ar2[j];
        if a_item < b_item {
            if result.len() == 0 || result[result.len() - 1] != a_item {
                result.push(a_item);
            }
            i += 1;
        } else if a_item > b_item {
            if result.len() == 0 || result[result.len() - 1] != b_item {
                result.push(b_item);
            }
            j += 1;
        } else {
            if result.len() == 0 || result[result.len() - 1] != a_item {
                result.push(a_item);
            }
            i += 1;
            j += 1;
        }
    }
    while i < ar1.len()
        invariant
            i <= ar1.len(),
            forall|k: int| i <= k < ar1.len() ==> 
                forall|m: int| 0 <= m < result.len() ==> result@[m] <= ar1@[k],
            forall|m: int, l: int| 0 <= m < l < result.len() ==> result@[m] <= result@[l],
            forall|m: int, l: int| 0 <= m < l < result.len() ==> result@[m] != result@[l],
    {
        if result.len() == 0 || result[result.len() - 1] != ar1[i] {
            result.push(ar1[i]);
        }
        i += 1;
    }
    while j < ar2.len()
        invariant
            j <= ar2.len(),
            forall|k: int| j <= k < ar2.len() ==> 
                forall|m: int| 0 <= m < result.len() ==> result@[m] <= ar2@[k],
            forall|m: int, l: int| 0 <= m < l < result.len() ==> result@[m] <= result@[l],
            forall|m: int, l: int| 0 <= m < l < result.len() ==> result@[m] != result@[l],
    {
        if result.len() == 0 || result[result.len() - 1] != ar2[j] {
            result.push(ar2[j]);
        }
        j += 1;
    }
    result
}
// </vc-code>


}
fn main() {}