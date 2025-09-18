// <vc-preamble>
use vstd::prelude::*;

verus! {

struct Complex {

    real: f64,

    imag: f64,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed vector_index_in_range parameter types to use int instead of usize */
proof fn vector_index_in_range<T>(v: &Vec<T>, i: int)
    requires
        0 <= i < v.len()
    ensures
        v[i] == v@[i]
{
}

proof fn helper_lemma_imag_nonzero(c: Complex) -> (b: bool)
    ensures b == (c.imag != 0.0)
{
    let b = c.imag != 0.0;
    b
}

proof fn helper_lemma_imag_zero(c: Complex) -> (b: bool)
    ensures b == (c.imag == 0.0)
{
    let b = c.imag == 0.0;
    b
}
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
/* code modified by LLM (iteration 5): Changed loop index back to int and fixed vector_index_in_range call */
{
    let mut result = Vec::new();
    let mut i: int = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (x[j].imag != 0.0),
            forall|j: int| 0 <= j < i ==> (x[j].imag == 0.0 ==> result[j] == false),
            forall|j: int| 0 <= j < i ==> (x[j].imag != 0.0 ==> result[j] == true),
            forall|j: int| 0 <= j < i ==> (result[j] == true ==> x[j].imag != 0.0),
            forall|j: int| 0 <= j < i ==> (result[j] == false ==> x[j].imag == 0.0)
        decreases x.len() - i
    {
        vector_index_in_range(x, i);
        let complex = &x[i];
        let has_imag = complex.imag != 0.0;
        result.push(has_imag);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}