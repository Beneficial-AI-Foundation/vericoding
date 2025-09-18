// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): define is_nan_f32 using built-in f32::is_nan */
spec fn is_nan_f32(x: f32) -> bool {
    f32::is_nan(x)
}
// </vc-helpers>

// <vc-spec>
spec fn is_nan_f32(x: f32) -> bool;

spec fn valid_indices_count(a: Seq<f32>) -> nat
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        if is_nan_f32(a[0]) {
            valid_indices_count(a.skip(1))
        } else {
            1 + valid_indices_count(a.skip(1))
        }
    }
}

spec fn has_valid_element(a: Seq<f32>) -> bool 
{
    valid_indices_count(a) > 0
}

spec fn all_nan(a: Seq<f32>) -> bool 
{
    valid_indices_count(a) == 0
}

spec fn contains_nan(a: Seq<f32>) -> bool
    decreases a.len()
{
    if a.len() == 0 {
        false
    } else {
        is_nan_f32(a[0]) || contains_nan(a.skip(1))
    }
}

fn nanmean(a: Vec<f32>) -> (result: f32)
    ensures 

        (has_valid_element(a@) ==> !is_nan_f32(result)) &&

        (all_nan(a@) ==> is_nan_f32(result)) &&

        (!is_nan_f32(result) ==> has_valid_element(a@)) &&

        (!contains_nan(a@) && a.len() > 0 ==> !is_nan_f32(result))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): change count to int and fix operations */
{
    let mut count: int = 0;
    let mut sum = 0.0;
    for i in 0..a.len()
        invariant 
            0 <= i <= a.len(),
            count == valid_indices_count(a@.subrange(0, i as int))
    {
        if !a[i].is_nan() {
            count += 1;
            sum += a[i];
        }
    }
    if count == 0 {
        f32::NAN
    } else {
        sum / (count as f32)
    }
}
// </vc-code>

}
fn main() {}