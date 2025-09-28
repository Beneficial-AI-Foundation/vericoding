// <vc-preamble>
use vstd::prelude::*;

verus! {

struct Complex {

    real: f64,

    imag: f64,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate for non-zero imaginary part */
fn imag_nonzero(c: Complex) -> bool { c.imag != 0.0 }

/* helper modified by LLM (iteration 5): convert usize to int for use in invariants */
spec fn usize_to_int(u: usize) -> int { u as int }
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
    /* code modified by LLM (iteration 5): iterate over vector and set res entries based on imag_nonzero */
    let mut res: Vec<bool> = Vec::new();
    let n: usize = x.len();
    let mut i: usize = 0;
    while i < n
        invariant
            res.len() == i,
            (i as int) <= x@.len(),
            forall|j: int| 0 <= j < (i as int) ==> res@[j] == (x@[j].imag != 0.0),
        decreases n - i
    {
        let b: bool = imag_nonzero(x[i]);
        res.push(b);
        i = i + 1;
    }
    res
}

// </vc-code>

}
fn main() {}