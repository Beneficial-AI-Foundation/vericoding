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
/* helper modified by LLM (iteration 5): fix lemma syntax by using proper ensures block with comma-separated conditions */
proof fn lemma_product_of_signs_is_sign(arr: Seq<int>)
    ensures 
        arr.len() == 0 ==> product_of_signs(arr) == 1,
        arr.len() > 0 ==> product_of_signs(arr) == sign(arr[0]) * product_of_signs(arr.subrange(1, arr.len() as int))
{
    if arr.len() == 0 {
        // product_of_signs(empty) = 1 by definition
    } else {
        // By the definition of product_of_signs, it is exactly sign(arr[0]) * product_of_signs(arr.subrange(1, arr.len() as int))
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
/* code modified by LLM (iteration 5): fix implementation to properly handle the case when product is zero */
{
    if arr.is_empty() {
        Option::<i8>::None
    } else {
        let mut sum: int = 0;
        let mut product: int = 1;
        let mut i: usize = 0;
        
        while i < arr.len()
            invariant 0 <= i <= arr.len(),
            invariant sum == sum_of_magnitudes(arr@.subrange(0, i as int).map(|x: i8| x as int)),
            invariant product == product_of_signs(arr@.subrange(0, i as int).map(|x: i8| x as int)),
            decreases arr.len() - i
        {
            let val = arr[i] as int;
            let abs_val = if val >= 0 { val } else { -val };
            let sign_val = if val > 0 { 1 } else if val < 0 { -1 } else { 0 };
            sum = sum + abs_val;
            product = product * sign_val;
            i = i + 1;
        }
        
        proof {
            lemma_sum_of_magnitudes_is_nonnegative(arr@.map(|x: i8| x as int));
        }
        
        let total = sum * product;
        Option::<i8>::Some(total as i8)
    }
}
// </vc-code>


}

fn main() {}