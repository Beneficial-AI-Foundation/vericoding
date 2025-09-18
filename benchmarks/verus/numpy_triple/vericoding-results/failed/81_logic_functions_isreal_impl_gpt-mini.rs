// <vc-preamble>
use vstd::prelude::*;

verus! {

struct Complex {

    real: f64,

    imag: f64,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate to check imaginary part is zero */
spec fn imag_is_zero(c: Complex) -> bool { c.imag == 0.0 }
// </vc-helpers>

// <vc-spec>
fn isreal(x: &Vec<Complex>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> result[i] == (x[i].imag == 0.0),
        forall|i: int| 0 <= i < x.len() ==> (x[i].imag == 0.0 ==> result[i] == true),
        forall|i: int| 0 <= i < x.len() ==> (x[i].imag != 0.0 ==> result[i] == false),
        forall|i: int| 0 <= i < x.len() ==> (result[i] == true ==> x[i].imag == 0.0),
        forall|i: int| 0 <= i < x.len() ==> (result[i] == false ==> x[i].imag != 0.0),
        forall|i: int| 0 <= i < x.len() ==> (result[i] == true ==> x[i].real == x[i].real),
        forall|i: int| 0 <= i < x.len() ==> result[i] == !(x[i].imag != 0.0),
        forall|i: int| 0 <= i < x.len() ==> (result[i] == true <==> x[i].imag == 0.0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build boolean vector indicating imag == 0.0 using while loop */
    let mut res: Vec<bool> = Vec::new();
    let len = x.len();
    let mut i = 0;
    while i < len {
        invariant res.len() == i;
        decreases len - i;
        let is_z: bool = x[i].imag == 0.0;
        res.push(is_z);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}