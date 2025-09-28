// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn last_idx_of(s: Seq<usize>, val: int, end: int) -> (res: int)
    recommends
        0 <= end <= s.len(),
    decreases end
{
    if end == 0 {
        -1
    } else if s[end-1] as int == val {
        end - 1
    } else {
        last_idx_of(s, val, end - 1)
    }
}

/* helper modified by LLM (iteration 2): Changed val type from usize to int to fix compilation errors */
spec fn has(s: Seq<usize>, val: int, end: int) -> bool {
    last_idx_of(s, val, end) >= 0
}
// </vc-helpers>

// <vc-spec>
fn put(a: Vec<f64>, ind: Vec<usize>, v: Vec<f64>) -> (result: Vec<f64>)
    requires 
        ind.len() == v.len(),
        forall|i: int| 0 <= i < ind@.len() ==> (ind[i] as int) < (a@.len() as int),
    ensures
        result@.len() == a@.len(),
        forall|i: int| 0 <= i < ind@.len() ==> result@[ind[i] as int] == v@[i],
        forall|j: int| 0 <= j < result@.len() ==> 
            (forall|i: int| 0 <= i < ind@.len() ==> j != ind[i] as int) ==> result@[j] == a@[j],
        ind@.len() == 0 ==> result@ == a@,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed compilation errors by using spec indexing and correct types in invariants. */
{
    let mut result = a;
    let mut i: usize = 0;
    while i < ind.len()
        invariant
            ind.len() == v.len(),
            result@.len() == a@.len(),
            forall|k: int| 0 <= k < ind@.len() ==> (ind@[k] as int) < result@.len(),
            i <= ind.len(),
            forall|j: int| 0 <= j < result@.len() ==> 
                if has(ind@, j, i as int) {
                    let k = last_idx_of(ind@, j, i as int);
                    k >= 0 && result@[j] == v@[k]
                } else {
                    result@[j] == a@[j]
                },
        decreases ind.len() - i
    {
        result.set(ind[i], v[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}