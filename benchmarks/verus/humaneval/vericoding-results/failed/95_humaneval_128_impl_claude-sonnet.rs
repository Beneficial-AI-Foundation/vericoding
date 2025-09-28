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
/* helper modified by LLM (iteration 5): Added trigger annotation to fix automatic trigger inference error */
proof fn sum_of_magnitudes_additive(arr: Seq<int>, i: int)
    requires 0 <= i < arr.len()
    ensures sum_of_magnitudes(arr) == abs(arr[i]) + sum_of_magnitudes(arr.subrange(0, i).add(arr.subrange(i + 1, arr.len() as int)))
    decreases arr.len()
{
}

proof fn product_of_signs_multiplicative(arr: Seq<int>, i: int)
    requires 0 <= i < arr.len()
    ensures product_of_signs(arr) == sign(arr[i]) * product_of_signs(arr.subrange(0, i).add(arr.subrange(i + 1, arr.len() as int)))
    decreases arr.len()
{
}

proof fn sum_of_magnitudes_bounds(arr: Seq<int>)
    requires #[trigger] forall|i: int| #[trigger] (0 <= i < arr.len()) ==> -128 <= arr[i] <= 127
    ensures sum_of_magnitudes(arr) <= 127 * arr.len()
    decreases arr.len()
{
    if arr.len() == 0 {
    } else {
        sum_of_magnitudes_bounds(arr.subrange(1, arr.len() as int));
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
    /* code modified by LLM (iteration 5): Fixed trigger syntax error */
    if arr.len() == 0 {
        return Option::<i8>::None;
    }
    
    let mut sum_mag: i16 = 0;
    let mut prod_sign: i8 = 1;
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            sum_mag == sum_of_magnitudes(arr@.subrange(0, i as int).map(|j: int, x: i8| x as int)),
            prod_sign == product_of_signs(arr@.subrange(0, i as int).map(|j: int, x: i8| x as int)),
            -128 <= sum_mag <= 127 * i,
            prod_sign == -1 || prod_sign == 0 || prod_sign == 1,
        decreases arr.len() - i
    {
        let val = arr[i];
        let abs_val = if val >= 0 { val } else { -val };
        sum_mag = sum_mag + abs_val as i16;
        
        if val > 0 {
            // prod_sign stays the same
        } else if val < 0 {
            prod_sign = -prod_sign;
        } else {
            prod_sign = 0;
        }
        
        i = i + 1;
    }
    
    let result = (sum_mag as i8) * prod_sign;
    Option::<i8>::Some(result)
}
// </vc-code>


}

fn main() {}