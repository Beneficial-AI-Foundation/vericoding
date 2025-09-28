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
fn is_complex(x: &Vec<Complex>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x@.len() ==> result@[i] == (x@[i].imag != 0.0),
        forall|i: int| 0 <= i < x@.len() ==> (x@[i].imag == 0.0 ==> result@[i] == false),
        forall|i: int| 0 <= i < x@.len() ==> (x@[i].imag != 0.0 ==> result@[i] == true),
        forall|i: int| 0 <= i < x@.len() ==> (result@[i] == true ==> x@[i].imag != 0.0),
        forall|i: int| 0 <= i < x@.len() ==> (result@[i] == false ==> x@[i].imag == 0.0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed loop invariant by adding additional invariants to match postconditions */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i as int <= x@.len(),
            result@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> result@[j] == (x@[j].imag != 0.0),
            forall|j: int| 0 <= j < i as int ==> (x@[j].imag == 0.0 ==> result@[j] == false),
            forall|j: int| 0 <= j < i as int ==> (x@[j].imag != 0.0 ==> result@[j] == true),
            forall|j: int| 0 <= j < i as int ==> (result@[j] == true ==> x@[j].imag != 0.0),
            forall|j: int| 0 <= j < i as int ==> (result@[j] == false ==> x@[j].imag == 0.0),
        decreases (x@.len() - i as int)
    {
        result.push(x[i].imag != 0.0);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}