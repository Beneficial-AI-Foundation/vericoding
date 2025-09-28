// <vc-preamble>
use vstd::prelude::*;

verus! {

struct Complex {

    real: f64,

    imag: f64,
}
// </vc-preamble>

// <vc-helpers>

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
/* code modified by LLM (iteration 5): Fixed loop invariant by using `x@.len()` instead of `x.len()` for the bound of `i`. */
{
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i as int <= x@.len() as int,
            result.len() == i as nat,
            forall|j: int| 0 <= j < i as int ==> result@[j] == (x@[j].imag == 0.0),
        decreases x.len() as int - i as int
    {
        result.push(x[i].imag == 0.0);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}