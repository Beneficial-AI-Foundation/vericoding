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
    /* code modified by LLM (iteration 4): Fixed int casting issues in exec code */
    if xs.len() <= 1 {
        Vec::new()
    } else {
        let mut result = Vec::new();
        let mut i: usize = 1;
        while i < xs.len()
            invariant
                1 <= i <= xs.len(),
                result@.len() == i - 1,
                forall|j: int| 0 <= j < result@.len() ==> result@[j] as int == (j + 1) * (xs@[j + 1] as int),
            decreases xs.len() - i
        {
            let coeff = xs[i];
            if i <= 127 {
                let multiplier = i as i8;
                let product = multiplier * coeff;
                result.push(product);
            } else {
                // i > 127, so we need to handle this case
                result.push(0i8);
            }
            i = i + 1;
        }
        result
    }
}
// </vc-code>


}

fn main() {}