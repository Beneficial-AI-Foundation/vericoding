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
/* helper modified by LLM (iteration 5): retain trivial lemma and expected derivative spec for potential proofs */
proof fn lemma_trivial()
    ensures
        true,
{
}

/* helper modified by LLM (iteration 5): spec function for expected derivative coefficients */
spec fn deriv_expected(xs: Seq<int>) -> Seq<int> {
    if xs.len() <= 1 {
        Seq::<int>::empty()
    } else {
        Seq::<int>::new((xs.len() - 1) as nat, |j: int| (j + 1) * xs[j + 1])
    }
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
    /* code modified by LLM (iteration 5): avoid exec 'int' usage; compute using i32 and cast to i8; maintain loop invariants */
    let n = xs.len();
    if n <= 1 {
        let result: Vec<i8> = Vec::new();
        return result;
    }

    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0usize;
    while i + 1 < n
        invariant
            xs@.len() == n as int,
            result@.len() == i as int,
            0 <= i as int,
            i as int <= xs@.len(),
        decreases xs@.len() - i as int
    {
        let x: i8 = xs[i + 1];
        let prod: i32 = ((i as i32) + 1) * (x as i32);
        let y: i8 = prod as i8;
        result.push(y);
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}