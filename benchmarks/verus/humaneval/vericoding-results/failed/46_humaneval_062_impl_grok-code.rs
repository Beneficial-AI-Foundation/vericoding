// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(xs: Seq<int>) -> bool {
    true  /* Any sequence of coefficients is valid input */
}

spec fn derivative_length(xs: Seq<int>) -> nat {
    if xs.len() <= 1 { 0nat } else { (xs.len() - 1) as nat }
}

spec fn correct_derivative_coefficients(xs: Seq<int>, result: Seq<int>) -> bool {
    xs.len() <= 1 ==> result == Seq::<int>::empty() &&
    xs.len() > 1 ==> (result.len() == xs.len() - 1 && 
                      forall|j: int| 0 <= j < result.len() ==> result[j] == (j + 1) * xs[j + 1])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Use int for index to avoid type issues in multiplication */
spec fn compute_coeff(i: int, xs: Seq<int>) -> int {
    i * xs[i as nat]
}
// </vc-helpers>

// <vc-spec>
fn derivative(xs: Vec<i8>) -> (result: Vec<i8>)
    requires 
        valid_input(xs@.map(|i: int, x: i8| x as int))
    ensures 
        correct_derivative_coefficients(xs@.map(|i: int, x: i8| x as int), result@.map(|i: int, x: i8| x as int)),
        result@.len() == derivative_length(xs@.map(|i: int, x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix indexing types and use helper consistently */
    let mut result = Vec::new();
    let ghost xs_seq = xs@.map(|i: int, x: i8| x as int);
    proof {
        assert(forall|j: int| 0 <= j < xs.len() ==> xs@[j] as int == xs_seq[j]);
    }
    if xs.len() <= 1 {
        // empty result
    } else {
        for i in 1..xs.len()
            invariant
                result@.len() == (i - 1) as nat,
                forall|j: int| 0 <= j < result@.len() ==> result@[j] as int == compute_coeff((j + 1) as int, xs_seq),
                decreases (xs.len() - i) as nat
        {
            let coeff_i = (compute_coeff(i as int, xs_seq) as i32) as i8;
            result.push(coeff_i);
        }
    }
    result
}
// </vc-code>


}

fn main() {}