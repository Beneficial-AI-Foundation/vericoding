// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma showing valid_indices_count does not exceed sequence length */
proof fn valid_indices_count_le_len(a: Seq<f32>) ensures valid_indices_count(a) <= a.len()
    decreases a.len()
{
    if a.len() == 0 {
    } else {
        if is_nan_f32(a[0]) {
            valid_indices_count_le_len(a.skip(1));
            assert(valid_indices_count(a) == valid_indices_count(a.skip(1)));
            assert(valid_indices_count(a.skip(1)) <= a.skip(1).len());
            assert(a.skip(1).len() + 1 == a.len());
            assert(valid_indices_count(a) <= a.len());
        } else {
            valid_indices_count_le_len(a.skip(1));
            assert(valid_indices_count(a) == 1 + valid_indices_count(a.skip(1)));
            assert(valid_indices_count(a.skip(1)) <= a.skip(1).len());
            assert(a.skip(1).len() + 1 == a.len());
            assert(valid_indices_count(a) <= a.len());
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
{
    /* code modified by LLM (iteration 5): compute mean ignoring NaNs using f32 count to avoid usize->f32 cast */
    let mut sum: f32 = 0.0;
    let mut count: f32 = 0.0;
    let mut i: usize = 0usize;
    while i < a.len()
        invariant i <= a.len()
        decreases a.len() - i
    {
        let v = a[i];
        if !v.is_nan() {
            sum = sum + v;
            count = count + 1.0;
        }
        i = i + 1;
    }
    if count == 0.0 {
        f32::NAN
    } else {
        sum / count
    }
}
// </vc-code>

}
fn main() {}