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
/* helper modified by LLM (iteration 3): [unchanged from previous turn] */
#[verifier::spinoff_prover]
proof fn lemma_real_is_close(arr: Seq<Complex>, tol: i32)
    requires
        tol > 0,
        forall|i: int| 0 <= i < arr.len() ==> arr[i].im == 0,
    ensures
        all_imaginary_parts_close_to_zero(arr, tol),
{
    assert forall|i: int| 0 <= i < arr.len() implies is_close_to_zero(arr[i], tol) by {};
}
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
    /* code modified by LLM (iteration 3): [fixed compilation errors: added type hint and manual copy] */
    let mut all_close = true;
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            all_close == forall|j: int| 0 <= j < i ==> is_close_to_zero(arr@[j], tol),
            tol > 0,
        decreases arr.len() - i
    {
        let c = &arr[i];

        // Use i64 to avoid overflow when multiplying, to match spec behavior using unbounded integers
        let im_val = c.im as i64;
        let abs_im = if im_val >= 0 { im_val } else { -im_val };
        
        let tol_val = tol as i64;

        // The check is |c.im| <= tol * machine_epsilon(), so we test for the negation
        // machine_epsilon() is defined as 2
        let not_close = abs_im > tol_val * 2;
        assert(not_close == !is_close_to_zero(*c, tol));

        if not_close {
            all_close = false;
        }
        
        i = i + 1;
    }

    let mut result: Vec<Complex> = Vec::new();
    let mut j = 0;
    while j < arr.len()
        invariant
            0 <= j <= arr.len(),
            result.len() == j,
            all_close == all_imaginary_parts_close_to_zero(arr@, tol),
            all_close ==> (forall|k: int| 0 <= k < j ==> result@[k].re == arr@[k].re && result@[k].im == 0),
            !all_close ==> (forall|k: int| 0 <= k < j ==> result@[k] == arr@[k]),
            forall|k: int| 0 <= k < j ==> result@[k].re == arr@[k].re,
        decreases arr.len() - j
    {
        let c = &arr[j];
        if all_close {
            let new_c = Complex { re: c.re, im: 0 };
            result.push(new_c);
        } else {
            result.push(Complex { re: c.re, im: c.im });
        }
        j = j + 1;
    }

    proof {
        if forall|idx: int| 0 <= idx < arr@.len() ==> arr@[idx].im == 0 {
            lemma_real_is_close(arr@, tol);
        }
    }

    result
}
// </vc-code>


}
fn main() {}