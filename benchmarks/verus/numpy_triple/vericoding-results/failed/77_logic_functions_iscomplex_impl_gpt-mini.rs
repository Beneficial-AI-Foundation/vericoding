// <vc-preamble>
use vstd::prelude::*;

verus! {

struct Complex {

    real: f64,

    imag: f64,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate checking whether complex.imag != 0.0 */
fn is_imag_nonzero(c: &Complex) -> bool { c.imag != 0.0 }
// </vc-helpers>

// <vc-spec>
fn is_complex(x: &Vec<Complex>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> result[i] == (x[i].imag != 0.0),
        forall|i: int| 0 <= i < x.len() ==> (x[i].imag == 0.0 ==> result[i] == false),
        forall|i: int| 0 <= i < x.len() ==> (x[i].imag != 0.0 ==> result[i] == true),
        forall|i: int| 0 <= i < x.len() ==> (result[i] == true ==> x[i].imag != 0.0),
        forall|i: int| 0 <= i < x.len() ==> (result[i] == false ==> x[i].imag == 0.0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build boolean vector indicating imag != 0.0 */
    let mut result: Vec<bool> = Vec::new();
    let mut i: int = 0;
    while i < x.len()
        invariant i <= x.len();
        invariant result.len() == i;
        invariant forall|j: int| 0 <= j < result.len() ==> result[j] == (x[j].imag != 0.0);
        decreases x.len() - i;
    {
        let b = is_imag_nonzero(&x[i]);
        result.push(b);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}