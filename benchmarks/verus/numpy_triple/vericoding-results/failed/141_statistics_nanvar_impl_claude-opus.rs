// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn mean(s: Seq<f32>) -> f32
    decreases s.len()
{
    if s.len() == 0 {
        0.0
    } else {
        s.fold_left(0.0, |acc: f32, x: f32| acc + x) / (s.len() as f32)
    }
}

spec fn variance(s: Seq<f32>, ddof: nat) -> f32
    decreases s.len()
{
    if s.len() <= ddof {
        f32::NAN
    } else {
        let m = mean(s);
        let sum_sq = s.fold_left(0.0, |acc: f32, x: f32| acc + (x - m) * (x - m));
        sum_sq / ((s.len() - ddof) as f32)
    }
}

/* helper modified by LLM (iteration 5): Fixed arithmetic operations to use standard operators */
fn compute_nanvar(a: &Vec<f32>, ddof: usize) -> (result: f32)
    ensures result == variance(a@, ddof as nat)
{
    if a.len() <= ddof {
        return f32::NAN;
    }
    
    let mut sum: f32 = 0.0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            sum == a@.subrange(0, i as int).fold_left(0.0, |acc: f32, x: f32| acc + x),
    {
        sum = sum + a[i];
        i = i + 1;
    }
    let mean_val = sum / (a.len() as f32);
    
    let mut sum_sq: f32 = 0.0;
    let mut j: usize = 0;
    while j < a.len()
        invariant
            0 <= j <= a.len(),
            sum_sq == a@.subrange(0, j as int).fold_left(0.0, |acc: f32, x: f32| {
                let diff = a@[j as int] - mean_val;
                acc + diff * diff
            }),
    {
        let diff = a[j] - mean_val;
        sum_sq = sum_sq + diff * diff;
        j = j + 1;
    }
    
    sum_sq / ((a.len() - ddof) as f32)
}
// </vc-helpers>

// <vc-spec>
fn nanvar(a: Vec<f32>, ddof: usize) -> (result: f32)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Calling helper function */
    compute_nanvar(&a, ddof)
}
// </vc-code>

}
fn main() {}