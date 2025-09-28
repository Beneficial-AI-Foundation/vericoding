// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): added trigger annotations to fix automatic inference error */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() <= i,
            forall|idx: int| 0 <= idx < result@.len() ==> exists|ai: int, bi: int| 0 <= ai < i && 0 <= bi < b@.len() && a@[ai] == b@[bi] && result@[idx] == a@[ai] #[trigger],
        decreases a.len() - i
    {
        let mut j = 0;
        let mut found = false;
        while j < b.len() && !found
            invariant
                j <= b.len(),
                found ==> exists|bi: int| 0 <= bi < j && a@[i as int] == b@[bi],
            decreases b.len() - j
        {
            if a[i] == b[j] {
                found = true;
            }
            j += 1;
        }
        if found {
            let mut already_in_result = false;
            let mut k = 0;
            while k < result.len() && !already_in_result
                invariant
                    k <= result.len(),
                    already_in_result ==> exists|ri: int| 0 <= ri < k && result@[ri] == a@[i as int],
                decreases result.len() - k
            {
                if result[k] == a[i] {
                    already_in_result = true;
                }
                k += 1;
            }
            if !already_in_result {
                result.push(a[i]);
            }
        }
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}