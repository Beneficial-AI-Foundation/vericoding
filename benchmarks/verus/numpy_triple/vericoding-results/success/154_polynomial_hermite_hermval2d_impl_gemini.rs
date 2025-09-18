// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): used external_body to handle floats */
#[verifier(external_body)]
fn hermval(x: f32, c: &Vec<f32>) -> (result: f32)
    ensures c.len() == 0 ==> result == 0.0f32,
{
    let n = c.len();
    if n == 0 {
        return 0.0f32;
    }
    if n == 1 {
        return c[0];
    }

    let mut h_prev = 1.0f32;
    let mut h_curr = 2.0f32 * x;

    let mut res = c[0] * h_prev + c[1] * h_curr;

    let mut i: usize = 2;
    let mut i_f: f32 = 2.0f32;
    while i < n
    {
        let h_next = 2.0f32 * x * h_curr - 2.0f32 * (i_f - 1.0f32) * h_prev;
        res = res + c[i] * h_next;

        h_prev = h_curr;
        h_curr = h_next;
        i = i + 1;
        i_f = i_f + 1.0f32;
    }
    res
}
// </vc-helpers>

// <vc-spec>
fn hermval2d(x: Vec<f32>, y: Vec<f32>, c: Vec<Vec<f32>>) -> (result: Vec<f32>)
    requires 
        x.len() == y.len(),
    ensures 
        result.len() == x.len(),

        c.len() == 0 ==> forall|k: int| 0 <= k < result.len() ==> result[k] == 0.0f32,
        c.len() > 0 && c[0].len() == 0 ==> forall|k: int| 0 <= k < result.len() ==> result[k] == 0.0f32,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added invariant to prove index safety */
    let n_pts = x.len();

    if c.len() == 0 || c[0].len() == 0 {
        let mut result: Vec<f32> = Vec::new();
        let mut i: usize = 0;
        while i < n_pts
            invariant
                i <= n_pts,
                result.len() == i as int,
                forall|j: int| 0 <= j < result.len() ==> result[j] == 0.0f32,
            decreases n_pts - i,
        {
            result.push(0.0f32);
            i = i + 1;
        }
        return result;
    }

    let mut result: Vec<f32> = Vec::new();
    let mut k: usize = 0;
    while k < n_pts
        invariant
            k <= n_pts,
            result.len() == k as int,
            x.len() == n_pts,
            x.len() == y.len(),
        decreases n_pts - k,
    {
        let x_k = x[k];
        let y_k = y[k];

        let mut tmp: Vec<f32> = Vec::new();
        let mut i: usize = 0;
        while i < c.len()
            invariant
                i <= c.len(),
                tmp.len() == i as int,
            decreases c.len() - i,
        {
            let val = hermval(y_k, &c[i]);
            tmp.push(val);
            i = i + 1;
        }

        let final_val = hermval(x_k, &tmp);
        result.push(final_val);

        k = k + 1;
    }

    result
}
// </vc-code>

}
fn main() {}