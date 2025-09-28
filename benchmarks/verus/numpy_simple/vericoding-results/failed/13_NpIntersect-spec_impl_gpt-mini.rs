// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): vec_contains returns whether x exists in v */
fn vec_contains(v: Vec<i8>, x: i8) -> (result: bool)
    ensures
        result == exists|k: int| 0 <= k < v@.len() && v@[k] == x,
{
    let result = exists|k: int| 0 <= k < v@.len() && v@[k] == x;
    result
}

/* helper modified by LLM (iteration 5): not_in_vec returns negation of vec_contains */
fn not_in_vec(v: Vec<i8>, x: i8) -> (result: bool)
    ensures
        result == !exists|k: int| 0 <= k < v@.len() && v@[k] == x,
{
    let result = !(exists|k: int| 0 <= k < v@.len() && v@[k] == x);
    result
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
    /* code modified by LLM (iteration 5): build intersection preserving uniqueness */
    let mut result: Vec<i8> = Vec::new();
    let mut i: nat = 0;
    while i < a@.len()
        invariant
            i <= a@.len(),
        decreases a@.len() - i
    {
        let ai: i8 = a@[i];
        if vec_contains(b.clone(), ai) && not_in_vec(result.clone(), ai) {
            result.push(ai);
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}