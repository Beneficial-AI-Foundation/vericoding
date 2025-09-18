// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed syntax by removing '@' from types, changed @[i] to [i] for Seq indexing */
fn calculate_weighted_sum(a: Seq<f32>, w: Seq<f32>) -> (result: f32)
    requires a.len() == w.len(), a.len() > 0,
      #[trigger] forall |i:int| 0<=i<w.len() ==> w[i] > 0.0
    ensures result > 0.0
{
    let mut sum = 0.0;
    for i in 0..a.len() {
        sum = sum + a[i] * w[i];
    }
    sum
}

/* helper modified by LLM (iteration 5): Fixed syntax by removing '@' from types, changed @[i] to [i] for Seq indexing */
fn sum_vec(vec: Seq<f32>) -> (f32, f32) {
    let mut sum = 0.0;
    let mut count = 0.0;
    for i in 0..vec.len() {
        sum = sum + vec[i];
        count = count + 1.0;
    }
    (sum, count)
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
    /* code modified by LLM (iteration 5): Used sequences via .view() for helpers, fixed calls to pass views */
    let mut result: f32;
    if let Some(w) = weights {
        let sum_a_w = calculate_weighted_sum(a.view(), w.view());
        let (sum_w, _) = sum_vec(w.view());
        proof {
            assert(sum_w > 0.0);
        }
        result = sum_a_w / sum_w;
    } else {
        let (s, c) = sum_vec(a.view());
        proof {
            assert(c > 0.0);
        }
        result = s / c;
    }
    result
}
// </vc-code>

}
fn main() {}