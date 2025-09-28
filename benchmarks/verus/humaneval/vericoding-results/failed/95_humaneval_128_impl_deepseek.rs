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
/* helper modified by LLM (iteration 5): Fixed syntax error in ensures clause */
fn prod_signs_helper(arr: &Vec<i8>, idx: int, len: int) -> (int, int)
    requires
        0 <= idx <= len,
        len == arr@.len(),
    ensures
        let (sum, prod) = result;
        sum == sum_of_magnitudes(arr@.subrange(idx, len)),
        prod == product_of_signs(arr@.subrange(idx, len)),
    decreases len - idx
{
    if idx == len {
        (0, 1)
    } else {
        let (next_sum, next_prod) = prod_signs_helper(arr, idx + 1, len);
        (abs(arr@[idx] as int) + next_sum, sign(arr@[idx] as int) * next_prod)
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
    /* code modified by LLM (iteration 5): Clean implementation without spec syntax */
    let len = arr.len();
    if len == 0 {
        Option::<i8>::None
    } else {
        let (total_sum, total_prod) = prod_signs_helper(&arr, 0, len);
        let result_val = (total_sum * total_prod) as i8;
        Option::<i8>::Some(result_val)
    }
}
// </vc-code>


}

fn main() {}