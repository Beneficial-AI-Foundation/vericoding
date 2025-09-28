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
/* helper modified by LLM (iteration 5): return integer view of Vec<i8> element */
spec fn vec_elem_as_int(xs: Vec<i8>, i: int) -> int
    requires
        0 <= i && i < xs@.len(),
    ensures
        result == (xs@.map(|k: int, x: i8| x as int))@[i],
{
    (xs@.map(|k: int, x: i8| x as int))@[i]
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
    /* code modified by LLM (iteration 5): compute polynomial derivative into Vec<i8> with loop invariants */
    let mut result = Vec::<i8>::new();
    let n = xs.len();
    if n <= 1 {
        return result;
    }
    let mut i: usize = 0;
    while i < n - 1
        invariant
            result@.len() == i as nat,
            forall|j: int| 0 <= j < i as int ==> result@[j] == (j + 1) * (xs@.map(|k: int, x: i8| x as int))@[j + 1],
        decreases n - 1 - i
    {
        let coeff_i = (i as i32 + 1) * (xs[i + 1] as i32);
        let v: i8 = coeff_i as i8;
        result.push(v);
        proof {
            assert(result@.len() == (i + 1) as nat);
            assert(result@[i as int] == (i as int + 1) * (xs@.map(|k: int, x: i8| x as int))@[(i as int) + 1]);
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}