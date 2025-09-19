// <vc-preamble>
use vstd::prelude::*;

verus! {

/* Structure representing a complex number with float components */
#[derive(PartialEq, Eq)]
pub struct Complex {
    /* The real part of the complex number */
    pub re: i32,
    /* The imaginary part of the complex number */
    pub im: i32,
}

/* Machine epsilon for Float (approximately 2.2204460492503131e-16) */
spec fn machine_epsilon() -> i32 {
    2
}
/* Helper function to check if a complex number's imaginary part is close to zero */
spec fn is_close_to_zero(c: Complex, tol: i32) -> bool {
    let abs_im = if c.im >= 0 { c.im as int } else { -(c.im as int) };
    abs_im <= (tol as int) * (machine_epsilon() as int)
}

/* Helper function to check if all imaginary parts in a complex vector are close to zero */
spec fn all_imaginary_parts_close_to_zero(arr: Seq<Complex>, tol: i32) -> bool {
    forall|i: int| 0 <= i < arr.len() ==> is_close_to_zero(arr[i], tol)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn real_if_close(arr: Vec<Complex>, tol: i32) -> (result: Vec<Complex>)
    requires tol > 0,
    ensures
        /* Primary behavior: if all imaginary parts are close to zero, return real parts only */
        all_imaginary_parts_close_to_zero(arr@, tol) ==> 
            forall|i: int| 0 <= i < result@.len() ==> result@[i].re == arr@[i].re && result@[i].im == 0,
        /* Otherwise, preserve original complex numbers */
        !all_imaginary_parts_close_to_zero(arr@, tol) ==> 
            forall|i: int| 0 <= i < result@.len() ==> result@[i] == arr@[i],
        /* Real parts are always preserved */
        forall|i: int| 0 <= i < result@.len() ==> result@[i].re == arr@[i].re,
        /* Sanity check: result vector has same length as input */
        result@.len() == arr@.len(),
        /* Mathematical property: if input is already real, output equals input */
        (forall|i: int| 0 <= i < arr@.len() ==> arr@[i].im == 0) ==> 
            forall|i: int| 0 <= i < result@.len() ==> result@[i] == arr@[i],
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