// <vc-preamble>
use vstd::prelude::*;

verus! {

struct Complex {

    real: f64,

    imag: f64,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate for zero imaginary part */
spec fn imag_is_zero(c: Complex) -> bool {
    c.imag == 0.0
}

/* helper modified by LLM (iteration 5): lemma stating (v == 0.0) equals !(v != 0.0) */
proof fn lemma_not_neq_equiv(v: f64)
    ensures
        (v == 0.0) == !(v != 0.0)
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
    /* code modified by LLM (iteration 5): avoid moving out of Vec elements by borrowing; maintain spec-linked invariant */
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            result.len() == i,
            (i as int) <= x@.len(),
            forall|k: int| 0 <= k < i as int ==> result@[k] == (x@[k].imag == 0.0),
        decreases (x.len() - i) as int
    {
        let xi = &x[i];
        let b = xi.imag == 0.0;
        let j = result.len();
        assert(j == i);
        result.push(b);
        proof {
            assert(x@[i as int].imag == xi.imag);
            assert(b == (x@[i as int].imag == 0.0));
            assert(result@[i as int] == (x@[i as int].imag == 0.0));
        }
        i = i + 1;
    }
    result
}

// </vc-code>

}
fn main() {}