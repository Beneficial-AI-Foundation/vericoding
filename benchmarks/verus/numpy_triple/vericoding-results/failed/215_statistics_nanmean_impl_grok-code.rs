// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    /* code modified by LLM (iteration 5): implement nanmean with loop to compute mean excluding NaN values */
    let mut count = 0;
    let mut sum = 0.0f32;
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            count == valid_indices_count(a@.take(i))
        decreases a.len() - i
    {
        if !is_nan_f32(a[i]) {
            count += 1;
            sum += a[i];
        }
        i += 1;
    }
    if count > 0 {
        let result = sum / (count as f32);
        proof {
            assert(!is_nan_f32(result));
        }
        result
    } else {
        let result = 0.0f32 / 0.0f32;
        proof {
            assert(is_nan_f32(result));
        }
        result
    }
}
// </vc-code>

}
fn main() {}