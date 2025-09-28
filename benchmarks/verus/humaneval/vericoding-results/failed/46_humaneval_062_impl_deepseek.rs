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

proof fn cast_multiplication_lemma(j: int, x: i8)  /* helper modified by LLM (iteration 5): Fix type cast */
    requires
        0 <= j, x as int >= -2147483648, x as int <= 2147483647,
    ensures
        (j + 1) * (x as int) == (j as i8) * x as int,
{
}

proof fn cast_index_lemma(xs_i: usize)
    ensures
        xs_i as int >= 0,
{
}

proof fn len_map_lemma(xs: Seq<i8>) 
    ensures
        xs.map(|i: int, x: i8| x as int).len() == xs.len(),
{
}

proof fn index_map_lemma(xs: Seq<i8>, j: int)
    requires
        0 <= j < xs.len(),
    ensures
        xs.map(|i: int, x: i8| x as int)[j] == xs[j] as int,
{
}

fn vec_len_helper(xs: &Vec<i8>) -> (len: usize)
    ensures
        len == xs@.len(),
{
    xs.len()
}

spec fn is_empty_spec(xs: Seq<int>) -> bool {
    xs.len() == 0
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
    /* code modified by LLM (iteration 5): Fix index casting in multiplication lemma call */
    let len = vec_len_helper(&xs);
    if len <= 1 {
        Vec::new()
    } else {
        let mut result: Vec<i8> = Vec::with_capacity(len - 1);
        let mut i: usize = 1;
        proof {
            len_map_lemma(xs@);
        }
        while i < len
            invariant
                1 <= i <= len,
                result@.len() == i - 1,
                forall|j: int| 0 <= j < result@.len() ==> result@[j] as int == (j + 1) * (xs@[j + 1] as int),
            decreases len - i,
        {
            let j = i - 1;
            proof {
                index_map_lemma(xs@, i as int);
                cast_index_lemma(i);
            }
            let coeff = (j as i8) * xs[i];
            result.push(coeff);
            proof {
                let result_len = result@.len() - 1;
                cast_multiplication_lemma(j as int, xs[i]);
                assert(result@[result_len] as int == (j + 1) * (xs@[j + 1] as int));
            }
            i += 1;
        }
        result
    }
}
// </vc-code>


}

fn main() {}