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
    /* code modified by LLM (iteration 5): Fixed type mismatches (nat to usize for array access, int to usize for loop bounds) */
    let mut result: Vec<i8> = Vec::new();

    if xs.len() <= 1 {
        return result;
    }

    let mut i: usize = 0;
    while i < xs.len() - 1
        invariant
            xs.len() >= 1 ==> result.len() == i,
            xs.len() >= 1 ==> forall|j: int| 0 <= j < i ==> result@[j] == ((j + 1) * xs@[j + 1]) as i8,
            i <= xs.len() - 1,
    {
        let coeff_val: i8 = (((i as int + 1) * xs[i + 1])) as i8;
        result.push(coeff_val);
        i = i + 1;
    }

    result
}
// </vc-code>


}

fn main() {}