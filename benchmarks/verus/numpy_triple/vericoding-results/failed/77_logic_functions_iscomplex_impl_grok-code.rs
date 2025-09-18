// <vc-preamble>
use vstd::prelude::*;

verus! {

struct Complex {

    real: f64,

    imag: f64,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes needed, no helpers required */
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
{
/* code modified by LLM (iteration 5): Fixed compilation error by using exec access x[index].imag instead of spec x@[index].imag in exec code */
    let mut index: usize = 0;
    let mut result = Vec::<bool>::new();
    while index < x.len()
        invariant
            result.len() == index,
            forall|i: int| 0 <= i < index ==> result@[i] == (x@[i].imag != 0.0),
    {
        result.push(x[index].imag != 0.0);
        index += 1;
    }
    result
}
// </vc-code>

}
fn main() {}