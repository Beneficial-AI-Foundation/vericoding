// <vc-preamble>
use vstd::prelude::*;

verus! {

struct Complex {

    real: f64,

    imag: f64,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): check if complex is real */
fn complex_is_real(c: &Complex) -> bool {
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
    /* code modified by LLM (iteration 5): use spec-level indexing x@ to compute flag and avoid relating runtime reference */
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> result@[j] == (x@[j].imag == 0.0),
        decreases x.len() - i
    {
        let flag: bool = x@[i as int].imag == 0.0;
        result.push(flag);
        proof {
            assert(result.len() == i + 1);
            assert(result@[i as int] == flag);
            assert(flag == (x@[i as int].imag == 0.0));
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}