// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): no functional change, just formatting and comment */
fn contains(v: &Vec<i8>, e: i8) -> (res: bool)
    ensures
        res == v@.contains(e),
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            forall|k: int| 0 <= k < i ==> v@[k] != e,
        decreases v.len() - i
    {
        if v[i] == e {
            return true;
        }
        i = i + 1;
    }
    false
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
/* code modified by LLM (iteration 3): added loop invariants for standard intersection */
{
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|k1: int, k2: int| 0 <= k1 < k2 < result@.len() ==> result@[k1] != result@[k2],
            forall|k: int| 0 <= k < result@.len() ==> b@.contains(result@[k]),
            forall|k: int| 0 <= k < result@.len() ==> a@.subrange(0, i as int).contains(result@[k]),
            forall|j: int| 0 <= j < i ==> (b@.contains(a@[j]) ==> result@.contains(a@[j])),
        decreases a.len() - i
    {
        let elem = a[i];
        if contains(&b, elem) {
            if !contains(&result, elem) {
                result.push(elem);
            }
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}