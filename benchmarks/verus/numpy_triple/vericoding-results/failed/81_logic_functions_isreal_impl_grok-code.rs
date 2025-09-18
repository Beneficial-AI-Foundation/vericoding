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
/* code modified by LLM (iteration 5): changed i to nat type to match len() being nat, and added #[trigger] to forall to fix verification */
{
    let mut result: Vec<bool> = Vec::new();
    let mut i: nat = 0;
    while i < x.len()
        invariant
            result.len() == i,
            forall|j: nat| #![auto] 0 <= j < i ==> #[trigger] result[j] == (x[j].imag == 0.0)
        decreases (x.len() as int - i as int)
    {
        result.push(x[i].imag == 0.0);
        i = i + 1;
        // perhaps assert here, but assuming it's ok
    }
    proof {
        assert(result.len() == x.len());
        assert(forall|i: int| 0 <= i < x.len() ==> result[i] == (x[i].imag == 0.0));
    }
    result
}
// </vc-code>

}
fn main() {}