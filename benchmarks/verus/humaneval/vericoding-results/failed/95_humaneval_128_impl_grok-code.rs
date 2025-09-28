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
fn exec_sum_magnitudes(arr: &Vec<i8>) -> (result: i64)
    ensures
        result as int == sum_of_magnitudes(arr@.map(|i: int, x: i8| x as int))
{
    /* helper modified by LLM (iteration 4): changed to i64 to prevent arithmetic overflow */
    let mut sum: i64 = 0;
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            sum as int == sum_of_magnitudes(arr@.map(|i: int, x: i8| x as int).subrange(0, i as int))
        decreases arr.len() - i
    {
        let mag: i64 = if arr[i] >= 0 { arr[i] as i64 } else { -(arr[i] as i64) };
        sum += mag;
        i += 1;
    }
    sum
}

fn exec_prod_signs(arr: &Vec<i8>) -> (result: i64)
    ensures
        result as int == product_of_signs(arr@.map(|i: int, x: i8| x as int))
{
    /* helper modified by LLM (iteration 4): changed to i64 to prevent arithmetic overflow */
    let mut prod: i64 = 1;
    let mut j: usize = 0;
    while j < arr.len()
        invariant
            0 <= j <= arr.len(),
            prod as int == product_of_signs(arr@.map(|i: int, x: i8| x as int).subrange(0, j as int))
        decreases arr.len() - j
    {
        let s: i64 = if arr[j] > 0 { 1 } else if arr[j] < 0 { -1 } else { 0 };
        prod *= s;
        j += 1;
    }
    prod
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
    /* code modified by LLM (iteration 4): used i64 for computations to prevent overflow, added truncate for cast */
    if arr.len() == 0 {
        Option::<i8>::None
    } else {
        let sum = exec_sum_magnitudes(&arr);
        let prod = exec_prod_signs(&arr);
        let combined: i64 = sum * prod;
        Option::<i8>::Some(#[verifier::truncate] (combined as i8))
    }
}
// </vc-code>


}

fn main() {}