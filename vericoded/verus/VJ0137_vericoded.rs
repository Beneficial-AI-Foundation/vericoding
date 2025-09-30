// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): retain simple identity helper for potential use and to satisfy helper section */
fn identity_i32(x: i32) -> i32 { x }
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn array_concat(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len() + b.len(),
        forall|i: int| 0 <= i && i < a.len() ==> result[i] == a[i],
        forall|i: int| 0 <= i && i < b.len() ==> result[i + a.len()] == b[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clauses for loops and assertions for indexing */
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            res.len() == i,
            forall|k: int| 0 <= k && k < i as int ==> res[k] == a[k],
        decreases (a.len() as int) - (i as int)
    {
        assert(i < a.len());
        let v = a[i];
        res.push(v);
        i = i + 1;
    }
    assert(res.len() == a.len());
    let start_len: usize = res.len();
    let mut j: usize = 0;
    while j < b.len()
        invariant
            j <= b.len(),
            res.len() == start_len + j,
            forall|k: int| 0 <= k && k < start_len as int ==> res[k] == a[k],
            forall|k: int| 0 <= k && k < j as int ==> res[k + start_len as int] == b[k],
        decreases (b.len() as int) - (j as int)
    {
        assert(j < b.len());
        let v = b[j];
        res.push(v);
        j = j + 1;
    }
    res
}
// </vc-code>

}
fn main() {}