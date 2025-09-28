// <vc-preamble>
use vstd::prelude::*;

verus! {

struct Complex {

    real: f64,

    imag: f64,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add helper for complex number imaginary part check */
fn is_zero_imag(c: Complex) -> bool {
    c.imag == 0.0
}
// </vc-helpers>

// <vc-spec>
fn isreal(x: &Vec<Complex>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x@.len() ==> result@[i] == (x@[i].imag == 0.0),
        forall|i: int| 0 <= i < x@.len() ==> (x@[i].imag == 0.0 ==> result@[i] == true),
        forall|i: int| 0 <= i < x@.len() ==> (x@[i].imag != 0.0 ==> result@[i] == false),
        forall|i: int| 0 <= i < x@.len() ==> (result@[i] == true ==> x@[i].imag == 0.0),
        forall|i: int| 0 <= i < x@.len() ==> (result@[i] == false ==> x@[i].imag != 0.0),
        forall|i: int| 0 <= i < x@.len() ==> (result@[i] == true ==> x@[i].real == x@[i].real),
        forall|i: int| 0 <= i < x@.len() ==> result@[i] == !(x@[i].imag != 0.0),
        forall|i: int| 0 <= i < x@.len() ==> (result@[i] == true <==> x@[i].imag == 0.0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix indexing and use helper function */
    let mut result = Vec::new();
    let mut i = 0;
    let n = x.len();
    while i < n
        invariant
            0 <= i <= n,
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == is_zero_imag(x@[j]),
        decreases n - i
    {
        result.push(is_zero_imag(x[i]));
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}