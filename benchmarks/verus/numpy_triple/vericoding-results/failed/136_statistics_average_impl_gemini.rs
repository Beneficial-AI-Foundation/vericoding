// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added requires/ensures/invariants for f32 finiteness */
fn vec_sum(v: &Vec<f32>) -> (sum: f32)
    requires
        forall|i: int| 0 <= i < v.len() ==> is_finite(v@[i]),
    ensures is_finite(sum),
{
    let mut sum = 0.0f32;
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            is_finite(sum),
        decreases v.len() - i
    {
        sum = sum + v[i];
        i = i + 1;
    }
    sum
}

/* helper modified by LLM (iteration 5): added requires/ensures/invariants for f32 finiteness */
fn weighted_sum(vals: &Vec<f32>, weights: &Vec<f32>) -> (sum: f32)
    requires
        vals.len() == weights.len(),
        forall|i: int| 0 <= i < vals.len() ==> is_finite(vals@[i]),
        forall|i: int| 0 <= i < weights.len() ==> is_finite(weights@[i]),
    ensures is_finite(sum),
{
    let mut sum = 0.0f32;
    let mut i: usize = 0;
    while i < vals.len()
        invariant
            i <= vals.len(),
            vals.len() == weights.len(),
            is_finite(sum),
        decreases vals.len() - i
    {
        sum = sum + vals[i] * weights[i];
        i = i + 1;
    }
    sum
}

/* helper modified by LLM (iteration 5): added ensures for non-zero result and invariant for finiteness */
fn usize_to_f32(u: usize) -> (res: f32)
    ensures
        is_finite(res),
        u > 0 ==> res > 0.0,
{
    let mut i: usize = 0;
    let mut f: f32 = 0.0;
    while i < u
        invariant 
            i <= u,
            is_finite(f),
        decreases u - i
    {
        f = f + 1.0;
        i = i + 1;
    }
    f
}
// </vc-helpers>

// <vc-spec>
fn average(a: Vec<f32>, weights: Option<Vec<f32>>) -> (result: f32)
    requires 
        a.len() > 0,
        match weights {
            Some(w) => w.len() == a.len(),
            None => true,
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added check for zero weight sum */
    match weights {
        None => {
            let total = vec_sum(&a);
            let len_f32 = usize_to_f32(a.len());
            total / len_f32
        },
        Some(w) => {
            let weighted_total = weighted_sum(&a, &w);
            let weights_total = vec_sum(&w);
            if weights_total == 0.0 {
                0.0
            } else {
                weighted_total / weights_total
            }
        },
    }
}
// </vc-code>

}
fn main() {}