// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 5): Replace predicate! with spec fn and use @ for indexing */
spec fn is_valid_idx_for(a: Seq<f32>, idx: int) -> bool {
    0 <= idx < a.len() && !is_nan_f32(a[idx])
}

spec fn sum_valid_elements(a: Seq<f32>) -> f32
    decreases a.len()
{
    if a.len() == 0 {
        0.0
    } else {
        if is_nan_f32(a[0]) {
            sum_valid_elements(a.skip(1))
        } else {
            a[0] + sum_valid_elements(a.skip(1))
        }
    }
}

proof fn valid_indices_count_decreases(a: Seq<f32>)
    ensures
        decreases(valid_indices_count(a))
{
    // Proof stub for termination
}

proof fn contains_nan_decreases(a: Seq<f32>)
    ensures
        decreases(contains_nan(a))
{
    // Proof stub for termination
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
{
    /* code modified by LLM (iteration 5): Mark is_nan_f32 as uninterp and fix loop bounds */
    let mut sum: f32 = 0.0;
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            count == valid_indices_count(a@.subrange(0, i as int)),
            sum == sum_valid_elements(a@.subrange(0, i as int)),
            count >= 0
    {
        if !is_nan_f32(a[i]) {
            sum = sum + a[i];
            count = count + 1;
        }
        i = i + 1;
    }
    
    if count > 0 {
        sum / (count as f32)
    } else {
        f32::NAN
    }
}
// </vc-code>

}
fn main() {}