// <vc-preamble>
use vstd::prelude::*;

verus! {

struct Complex {

    real: f64,

    imag: f64,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed lemma syntax by removing 'lemma' keyword from function name */
fn lemma_isreal_property(x: &Vec<Complex>, result: &Vec<bool>, i: usize)
    requires
        i < x.len(),
        result.len() > i,
        result@[i as int] == (x@[i as int].imag == 0.0),
    ensures
        result@[i as int] == (x@[i as int].imag == 0.0),
{
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
    /* code modified by LLM (iteration 5): kept simple implementation without proof blocks */
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == (x@[j].imag == 0.0),
        decreases x.len() - i
    {
        let is_real = x[i].imag == 0.0;
        result.push(is_real);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}