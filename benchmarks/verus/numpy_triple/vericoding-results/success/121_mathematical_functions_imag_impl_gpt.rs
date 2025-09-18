// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added spec accessor for imaginary component */
spec fn imag_of(p: (f64, f64)) -> f64 { p.1 }
// </vc-helpers>

// <vc-spec>
fn imag(val: Vec<(f64, f64)>) -> (result: Vec<f64>)
    ensures
        result.len() == val.len(),
        forall|i: int| 0 <= i < val.len() ==> result[i] == val[i].1,
        forall|i: int| 0 <= i < val.len() ==> (val[i].1 == 0.0 ==> result[i] == 0.0),
        forall|i: int| 0 <= i < val.len() ==> (val[i].0 != 0.0 || val[i].1 != 0.0 ==> result[i] == val[i].1),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fix invariant indexing to use int indices and maintain length relation */
    let n = val.len();
    let mut out: Vec<f64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == val.len(),
            out.len() == i,
            forall|j: int| 0 <= j < i as int ==> out[j] == val[j].1
        decreases n - i
    {
        let p = val[i];
        out.push(p.1);
        i = i + 1;
    }
    out
}
// </vc-code>

}
fn main() {}