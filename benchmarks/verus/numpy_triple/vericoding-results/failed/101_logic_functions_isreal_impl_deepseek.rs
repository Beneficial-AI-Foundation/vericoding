// <vc-preamble>
use vstd::prelude::*;

verus! {

struct Complex {

    real: f64,

    imag: f64,
}
// </vc-preamble>

// <vc-helpers>
fn check_complex_is_real(c: &Complex) -> (b: bool)
    ensures
        b == (c.imag == 0.0),
{
    /* helper modified by LLM (iteration 5): simplified implementation */
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
    /* code modified by LLM (iteration 5): simplified loop invariant */
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < x.len()
        invariant
            0 <= i <= x@.len(),
            result@.len() == i,
            forall|k: int| 0 <= k < i ==> result@[k] == (x@[k].imag == 0.0),
        decreases x@.len() - i,
    {
        let c = &x[i];
        let is_real_entry = c.imag == 0.0;
        result.push(is_real_entry);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}