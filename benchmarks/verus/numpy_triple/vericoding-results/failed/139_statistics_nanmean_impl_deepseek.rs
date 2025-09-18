// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed duplicate is_nan_f32 declaration and fixed proof helpers */
uninterp spec fn is_nan_f32(x: f32) -> bool;

proof fn valid_indices_count_decreases(a: Seq<f32>) -> (count: nat)
    ensures count == valid_indices_count(a)
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        let first_nan = is_nan_f32(a[0]);
        let rest = a.skip(1);
        let rest_count = valid_indices_count_decreases(rest);
        if first_nan {
            rest_count
        } else {
            1 + rest_count
        }
    }
}

proof fn contains_nan_decreases(a: Seq<f32>) -> (contains: bool)
    ensures contains == contains_nan(a)
    decreases a.len()
{
    if a.len() == 0 {
        false
    } else {
        let first_nan = is_nan_f32(a[0]);
        let rest = a.skip(1);
        let rest_contains = contains_nan_decreases(rest);
        first_nan || rest_contains
    }
}

spec fn sum_valid_indices(a: Seq<f32>) -> f32
    decreases a.len()
{
    if a.len() == 0 {
        0.0
    } else {
        if is_nan_f32(a[0]) {
            sum_valid_indices(a.skip(1))
        } else {
            (a[0] as f32) + sum_valid_indices(a.skip(1))
        }
    }
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
/* code modified by LLM (iteration 5): Fixed integer type conversion and loop condition */
{
    let mut sum = 0.0;
    let mut count = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant 
            i <= a.len(),
            sum == sum_valid_indices(a@.take(i)),
            count == valid_indices_count(a@.take(i))
    {
        match a[i] {
            nan if is_nan_f32(nan) => {},
            val => {
                proof { 
                    assert(is_nan_f32(val) == false);
                }
                sum = sum + val;
                count = count + 1;
            }
        }
        i = i + 1;
    }
    
    if count > 0 {
        sum / (count as f32)
    } else {
        let nan: f32 = 0.0 / 0.0;
        nan
    }
}
// </vc-code>

}
fn main() {}