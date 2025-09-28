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
    /* code modified by LLM (iteration 2): fixed quantifier trigger by removing map and using casting */
    if xs.len() <= 1 {
        Vec::new()
    } else {
        let mut result = Vec::new();
        let len = xs.len();
        let mut j = 0;
        while j < len - 1
            invariant
                0 <= j <= len - 1,
                result@.len() == j,
                forall|k: int| 0 <= k < j ==> 
                    (result@[k] as int) == (k+1) * (xs@[k+1] as int),
            decreases len - 1 - j
        {
            let index_plus_one = (j+1) as i64;
            let coeff = xs[j+1] as i64;
            let product = index_plus_one * coeff;
            result.push(product as i8);
            j += 1;
        }
        result
    }
}
// </vc-code>


}

fn main() {}