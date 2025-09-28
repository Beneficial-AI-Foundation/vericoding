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
{
    /* code modified by LLM (iteration 5): fixed type mismatch by making len int, used correct indexing with @ for Seq access */
    let x_seq = x@;
    let len = x_seq.len() as int;
    let mut result = Vec::new();
    let mut i: int = 0;
    while i < len
        invariant
            result@.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> result@[j] == (x_seq@[j].imag == 0.0),
        decreases len - i
    {
        result.push(x_seq@[i].imag == 0.0);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}