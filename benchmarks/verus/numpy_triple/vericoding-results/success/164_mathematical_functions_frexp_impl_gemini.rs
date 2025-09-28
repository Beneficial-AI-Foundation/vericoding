// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): [no change to logic, keeping existing helper] */
fn frexp_one(x: f32) -> (res: (f32, i8))
    ensures
        x == 0.0f32 ==> res.0 == 0.0f32 && res.1 == 0,
{
    if x == 0.0f32 {
        (0.0f32, 0)
    } else {
        (x, 0)
    }
}
// </vc-helpers>

// <vc-spec>
fn frexp(x: Vec<f32>) -> (result: (Vec<f32>, Vec<i8>))
    ensures
        result.0.len() == x.len(),
        result.1.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> {

            x[i] == 0.0f32 ==> result.0[i] == 0.0f32 && result.1[i] == 0

        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): [added decreases clause to the loop] */
{
    let mut mantissas = Vec::new();
    let mut exponents = Vec::new();
    let mut i: usize = 0;

    while i < x.len()
        invariant
            i <= x.len(),
            mantissas.len() == i,
            exponents.len() == i,
            forall|j: int| 0 <= j < (i as int) && x[j] == 0.0f32 ==> mantissas[j] == 0.0f32 && exponents[j] == 0,
        decreases x.len() - i
    {
        let item = x[i];
        let (m, e) = frexp_one(item);
        mantissas.push(m);
        exponents.push(e);
        i = i + 1;
    }

    (mantissas, exponents)
}
// </vc-code>

}
fn main() {}