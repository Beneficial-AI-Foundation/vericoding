// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): trivial lemma placeholder */
fn lemma_index_in_bounds<T>(v: Vec<T>, i: int)
    requires
        0 <= i < v.len(),
    ensures
        v[i as int] == v[i as int],
{
    proof {
        // trivial by reflexivity
    }
}
// </vc-helpers>

// <vc-spec>
fn imag(val: Vec<(f64, f64)>) -> (result: Vec<f64>)
    ensures
        result.len() == val.len(),
        forall|i: int| 0 <= i < val.len() ==> result[i as int] == val[i as int].1,
        forall|i: int| 0 <= i < val.len() ==> (val[i as int].1 == 0.0 ==> result[i as int] == 0.0),
        forall|i: int| 0 <= i < val.len() ==> (val[i as int].0 != 0.0 || val[i as int].1 != 0.0 ==> result[i as int] == val[i as int].1),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): iterate with usize and push imaginary parts */
    let mut result: Vec<f64> = Vec::new();
    let mut i: usize = 0;
    while i < val.len()
        invariant
            i <= val.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result[j as int] == val[j as int].1,
        decreases val.len() - i
    {
        let pair = val[i];
        result.push(pair.1);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}