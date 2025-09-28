// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

spec fn sign(x: int) -> int {
    if x > 0 { 1 } else if x < 0 { -1 } else { 0 }
}

spec fn sum_of_magnitudes(arr: Seq<int>) -> int
    decreases arr.len()
{
    if arr.len() == 0 { 0 } else { abs(arr[0]) + sum_of_magnitudes(arr.subrange(1, arr.len() as int)) }
}

spec fn product_of_signs(arr: Seq<int>) -> int
    decreases arr.len()
{
    if arr.len() == 0 { 1 } else { sign(arr[0]) * product_of_signs(arr.subrange(1, arr.len() as int)) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): no modifications needed */
#[verifier::spinoff_prover]
proof fn lemma_sum_append(s1: Seq<int>, s2: Seq<int>)
    ensures sum_of_magnitudes(s1 + s2) == sum_of_magnitudes(s1) + sum_of_magnitudes(s2),
    decreases s1.len()
{
    if s1.len() > 0 {
        lemma_sum_append(s1.subrange(1, s1.len() as int), s2);
    }
}

/* helper modified by LLM (iteration 4): no modifications needed */
#[verifier::spinoff_prover]
proof fn lemma_prod_append(s1: Seq<int>, s2: Seq<int>)
    ensures product_of_signs(s1 + s2) == product_of_signs(s1) * product_of_signs(s2),
    decreases s1.len()
{
    if s1.len() > 0 {
        lemma_prod_append(s1.subrange(1, s1.len() as int), s2);
    }
}
// </vc-helpers>

// <vc-spec>
fn prod_signs(arr: Vec<i8>) -> (result: Option<i8>)
    ensures 
        (arr@.len() == 0) ==> (result == Option::<i8>::None) &&
        (arr@.len() > 0) ==> (result == Option::<i8>::Some((sum_of_magnitudes(arr@.map(|i: int, x: i8| x as int)) * product_of_signs(arr@.map(|i: int, x: i8| x as int))) as i8))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): replaced unsupported .abs() and .signum() methods to fix compilation */
    if arr.len() == 0 {
        return Option::None;
    }

    let mut sum_mag: i64 = 0;
    let mut prod_sign: i64 = 1;
    let mut i: usize = 0;

    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            sum_mag as int == sum_of_magnitudes(arr@.map(|idx, x| x as int).subrange(0, i as int)),
            prod_sign as int == product_of_signs(arr@.map(|idx, x| x as int).subrange(0, i as int)),
        decreases arr.len() - i
    {
        let x = arr[i];
        
        let magnitude = if x == -128i8 { 128i64 } else if x >= 0 { x as i64 } else { -(x as i64) };
        sum_mag = sum_mag + magnitude;
        
        let sign_val = if x > 0 { 1i64 } else if x < 0 { -1i64 } else { 0i64 };
        prod_sign = prod_sign * sign_val;
        
        proof {
            let int_seq = arr@.map(|idx, x: i8| x as int);
            let sub_before = int_seq.subrange(0, i as int);
            let elem_seq = seq![int_seq[i as int]];
            
            lemma_sum_append(sub_before, elem_seq);
            lemma_prod_append(sub_before, elem_seq);

            let x_int = x as int;
            assert(magnitude as int == abs(x_int));
            assert(sign_val as int == sign(x_int));
        }

        i = i + 1;
    }

    let result = (sum_mag * prod_sign) as i8;
    Option::Some(result)
}

// </vc-code>


}

fn main() {}