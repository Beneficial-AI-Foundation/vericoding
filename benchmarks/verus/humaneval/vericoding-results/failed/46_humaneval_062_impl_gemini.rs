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
/* helper modified by LLM (iteration 5): no new helpers needed */
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
    /* code modified by LLM (iteration 5): corrected syntax for ghost let bindings */
    let n = xs.len();
    if n <= 1 {
        return Vec::new();
    }

    let mut result = Vec::<i8>::new();
    let mut i: usize = 0;
    while i < n - 1
        invariant
            n == xs.len(),
            n > 1,
            0 <= i <= n - 1,
            result.len() == i,
            forall|j: int| 0 <= j < i ==>
                (result@[j] as int) == (j + 1) * (xs@[j + 1] as int),
        decreases (n - 1) - i
    {
        let ghost i_int = i as int;
        let ghost product = (i_int + 1) * (xs@[i_int + 1] as int);
        
        assert(i8::MIN as int <= product && product <= i8::MAX as int);

        let val = (i + 1) as i128 * (xs[i + 1] as i128);
        assert(val == product);
        
        let new_coeff = val as i8;
        result.push(new_coeff);

        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}