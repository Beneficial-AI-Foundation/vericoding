// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): sum elements of vector */
fn sum_f32(v: Vec<f32>) -> f32 {
    let mut s: f32 = 0.0;
    let mut i: usize = 0;
    while i < v.len()
        invariant i <= v.len()
        decreases v.len() - i
    {
        proof {
            assert(i < v.len());
        }
        s = s + v[i];
        i += 1;
    }
    s
}

/* helper modified by LLM (iteration 5): dot product of two vectors */
fn dot_product(a: Vec<f32>, w: Vec<f32>) -> f32
    requires a.len() == w.len()
{
    let mut s: f32 = 0.0;
    let mut i: usize = 0;
    while i < a.len()
        invariant i <= a.len() && i <= w.len()
        decreases a.len() - i
    {
        proof {
            assert(i < a.len());
            assert(i < w.len());
        }
        s = s + a[i] * w[i];
        i += 1;
    }
    s
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
    /* code modified by LLM (iteration 5): compute weighted or unweighted average without usize->f32 cast */
    match weights {
        Some(w) => {
            let len = a.len();
            let mut i: usize = 0;
            let mut dot: f32 = 0.0;
            let mut sw: f32 = 0.0;
            while i < len
                invariant i <= len && i <= w.len()
                decreases len - i
            {
                proof {
                    assert(i < len);
                    assert(i < w.len());
                }
                dot = dot + a[i] * w[i];
                sw = sw + w[i];
                i += 1;
            }
            if sw == 0.0 {
                0.0
            } else {
                dot / sw
            }
        }
        None => {
            let len = a.len();
            let s = sum_f32(a);
            let mut n_f32: f32 = 0.0;
            let mut i: usize = 0;
            while i < len
                invariant i <= len
                decreases len - i
            {
                n_f32 = n_f32 + 1.0;
                i += 1;
            }
            s / n_f32
        }
    }
}
// </vc-code>

}
fn main() {}