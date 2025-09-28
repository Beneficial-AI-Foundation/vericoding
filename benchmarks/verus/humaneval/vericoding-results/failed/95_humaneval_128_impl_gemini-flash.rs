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

// </vc-helpers>

// <vc-spec>
fn prod_signs(arr: Vec<i8>) -> (result: Option<i8>)
    ensures 
        (arr@.len() == 0) ==> (result == Option::<i8>::None) &&
        (arr@.len() > 0) ==> (result == Option::<i8>::Some((sum_of_magnitudes(arr@.map(|i: int, x: i8| x as int)) * product_of_signs(arr@.map(|i: int, x: i8| x as int))) as i8))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation errors related to `nat`, `len()`, and sequence indexing. */
{
    if arr@.len() == 0 {
        Option::<i8>::None
    } else {
        let mut sum_magnitude: i8 = 0;
        let mut prod_sign: i8 = 1;
        let mut i: nat = 0 nat;

        while i < arr@.len()
            invariant
                sum_magnitude == sum_of_magnitudes(arr@.subrange(0, i as int).map(|idx: int, x: i8| x as int)) as i8,
                prod_sign == product_of_signs(arr@.subrange(0, i as int).map(|idx: int, x: i8| x as int)) as i8,
                i <= arr@.len(),
            decreases arr@.len() - i
        {
            let val_i8: i8 = arr.get(i);
            sum_magnitude = sum_magnitude + val_i8.abs();
            prod_sign = prod_sign * val_i8.signum();
            i = i + 1 nat;
        }

        let final_result_i8 = sum_magnitude * prod_sign;

        Option::<i8>::Some(final_result_i8)
    }
}
// </vc-code>


}

fn main() {}