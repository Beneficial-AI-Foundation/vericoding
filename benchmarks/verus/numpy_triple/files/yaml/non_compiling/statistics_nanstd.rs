/* Compute the standard deviation along the specified axis, ignoring NaNs.
Returns the standard deviation, a measure of the spread of a distribution,
of the non-NaN array elements. The standard deviation is the square root
of the variance computed from non-NaN values.

For all-NaN slices, NaN is returned. */

use vstd::prelude::*;

verus! {
spec fn valid_indices(a: Seq<f32>) -> Seq<int>
    decreases a.len()
{
    if a.len() == 0 {
        seq![]
    } else {
        let rest = valid_indices(a.skip(1));
        if !a[0].is_nan() {
            seq![0] + rest.map(|i: int| i + 1)
        } else {
            rest.map(|i: int| i + 1)
        }
    }
}

spec fn valid_sum(a: Seq<f32>, indices: Seq<int>) -> f32
    decreases indices.len()
{
    if indices.len() == 0 {
        0.0
    } else {
        a[indices[0]] + valid_sum(a, indices.skip(1))
    }
}

spec fn valid_mean(a: Seq<f32>, indices: Seq<int>) -> f32 {
    if indices.len() > 0 {
        valid_sum(a, indices) / (indices.len() as f32)
    } else {
        0.0
    }
}

spec fn squared_deviations_sum(a: Seq<f32>, indices: Seq<int>, mean: f32) -> f32
    decreases indices.len()
{
    if indices.len() == 0 {
        0.0
    } else {
        let val = a[indices[0]];
        let dev = val - mean;
        dev * dev + squared_deviations_sum(a, indices.skip(1), mean)
    }
}

fn nanstd(a: Vec<f32>, ddof: usize) -> (result: f32)
    ensures
        {
            let valid_idxs = valid_indices(a@);
            let valid_count = valid_idxs.len();
            if valid_count > 0 && ddof < valid_count {
                let mean = valid_mean(a@, valid_idxs);
                let variance = squared_deviations_sum(a@, valid_idxs, mean) / ((valid_count - ddof) as f32);
                result == variance.sqrt() &&
                result >= 0.0 &&
                !result.is_nan()
            } else {
                result.is_nan()
            }
        }
{
    // impl-start
    assume(false);
    0.0
    // impl-end
}
}
fn main() {}