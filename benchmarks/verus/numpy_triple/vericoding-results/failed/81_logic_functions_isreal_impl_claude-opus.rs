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
    /* code modified by LLM (iteration 5): Fix indexing - use x[i] instead of x@[i as int] */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (x[j].imag == 0.0)
        decreases x.len() - i
    {
        let is_real = x[i].imag == 0.0;
        result.push(is_real);
        assert(result.len() == i + 1);
        assert(result[i as int] == is_real);
        assert(result[i as int] == (x[i].imag == 0.0));
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}