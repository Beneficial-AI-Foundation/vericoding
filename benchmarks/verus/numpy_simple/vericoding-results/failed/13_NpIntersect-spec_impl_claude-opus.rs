// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added helper predicates for cleaner invariants */
spec fn element_in_seq(elem: i8, s: Seq<i8>) -> bool {
    exists|j: int| 0 <= j < s.len() && s[j] == elem
}

spec fn element_at_index_in_result(a: Seq<i8>, idx: int, result: Seq<i8>) -> bool {
    exists|k: int| 0 <= k < result.len() && result[k] == a[idx]
}
// </vc-helpers>

// <vc-spec>
fn intersect(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() < a.len() && result.len() < b.len(),
        forall|i: int, j: int| 0 <= i < a@.len() && 0 <= j < b@.len() ==> (
            (a@[i] == b@[j] ==> exists|k: int| 0 <= k < result@.len() && result@[k] == a@[i]) &&
            (a@[i] != b@[j] ==> !exists|k: int| 0 <= k < result@.len() && result@[k] == a@[i])
        )
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed trigger syntax - removed ||| operator */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() <= i,
            result.len() < a.len(),
            result.len() < b.len(),
            forall|idx: int| 0 <= idx < i ==> #[trigger] a@[idx],
            forall|idx: int| 0 <= idx < i ==> (
                element_in_seq(a@[idx], b@) ==> element_at_index_in_result(a@, idx, result@)
            ),
            forall|idx: int| 0 <= idx < i ==> (
                !element_in_seq(a@[idx], b@) ==> !element_at_index_in_result(a@, idx, result@)
            ),
            forall|k: int| 0 <= k < result@.len() ==> #[trigger] result@[k],
            forall|k: int| 0 <= k < result@.len() ==> (
                exists|idx: int| 0 <= idx < i && result@[k] == a@[idx] &&
                element_in_seq(result@[k], b@)
            ),
        decreases a.len() - i
    {
        let mut found = false;
        let mut j = 0;
        
        while j < b.len()
            invariant
                j <= b.len(),
                found == exists|jdx: int| 0 <= jdx < j && b@[jdx] == a@[i as int],
            decreases b.len() - j
        {
            if a[i] == b[j] {
                found = true;
                break;
            }
            j = j + 1;
        }
        
        if found {
            result.push(a[i]);
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}