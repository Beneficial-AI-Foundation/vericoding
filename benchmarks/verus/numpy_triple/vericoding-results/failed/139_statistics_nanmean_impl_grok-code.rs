// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed invalid 'uninterp' keyword for proper Verus syntax */
spec fn is_nan_f32(x: f32) -> bool;

spec fn prefix_valid_sum(s: Seq<f32>, i: nat) -> real
    requires i <= s.len()
    decreases i
{
    if i == 0 {
        0.0
    } else {
        let add = if is_nan_f32(s[i-1]) { 0.0 } else { s[i-1] as real };
        add + prefix_valid_sum(s, i-1)
    }
}
spec fn prefix_valid_count(s: Seq<f32>, i: nat) -> nat
    requires i <= s.len()
    decreases i
{
    if i == 0 {
        0nat
    } else {
        let add = if is_nan_f32(s[i-1]) { 0nat } else { 1nat };
        add + prefix_valid_count(s, i-1)
    }
}
exec fn compute_valid_sum(a: &Vec<f32>, i: usize) -> (result: f32)
    requires i <= a.len()
    ensures (result as real) == prefix_valid_sum(a@, i as nat)
    decreases i
{
    if i == 0 {
        0.0
    } else {
        let val = a[i-1];
        let add = if is_nan_f32(val) { 0.0 } else { val };
        add + compute_valid_sum(a, i-1)
    }
}
exec fn compute_valid_count(a: &Vec<f32>, i: usize) -> (result: nat)
    requires i <= a.len()
    ensures result == prefix_valid_count(a@, i as nat)
    decreases i
{
    if i == 0 {
        0nat
    } else {
        let val = a[i-1];
        let add: nat = if is_nan_f32(val) { 0nat } else { 1nat };
        add + compute_valid_count(a, i-1)
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
/* code modified by LLM (iteration 5): Retained nanmean implementation for NaN handling */
{
    let sum = compute_valid_sum(&a, a.len());
    let count = compute_valid_count(&a, a.len());
    let result = if count == 0 {
        0.0f32 / 0.0f32
    } else {
        let count_f32 = (count as int) as f32;
        sum / count_f32
    };
    result
}
// </vc-code>

}
fn main() {}