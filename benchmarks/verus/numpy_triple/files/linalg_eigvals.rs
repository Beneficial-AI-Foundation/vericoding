// <vc-preamble>
use vstd::prelude::*;

verus! {
/* Complex number type for eigenvalues */
struct Complex {
    re: f64,
    im: f64,
}

/* Matrix represented as a vector of vectors (rows) */
type Matrix<T> = Vec<Vec<T>>;
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn eigvals(a: &Matrix<f64>) -> (result: Vec<Complex>)
    requires 
        a@.len() > 0,
        forall|i: int| 0 <= i < a@.len() ==> a@[i].len() == a@.len(),
    ensures
        result@.len() == a@.len()
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}