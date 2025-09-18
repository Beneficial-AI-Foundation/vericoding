// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [fixed while loop invariant syntax by removing braces] */
fn find_interval_exec(x_val: i32, xp: &Vec<i32>) -> (i: usize)
    requires
        xp.len() >= 2,
        forall|i: int, j: int| 0 <= i < j < xp.len() ==> xp@[i] < xp@[j],
        xp@[0] <= x_val,
        x_val < xp@[xp.len() - 1],
    ensures
        i < xp.len() - 1,
        xp@[i] <= x_val < xp@[i + 1],
{
    let mut i: usize = 0;
    while i < xp.len() - 1
        decreases xp.len() - 1 - i
        invariant
            0 <= i < xp.len(),
            xp.len() >= 2,
            forall|k: int, l: int| 0 <= k < l < xp.len() ==> xp@[k] < xp@[l],
            forall|k: int| 0 <= k < i ==> xp@[k + 1] <= x_val,
            xp@[0] <= x_val,
            x_val < xp@[xp.len() - 1],
    {
        if xp[i + 1] > x_val {
            return i;
        }
        i = i + 1;
    }
    unreachable()
}
// </vc-helpers>

// <vc-spec>
fn interp(x: Vec<i32>, xp: Vec<i32>, fp: Vec<i32>) -> (result: Vec<i32>)
    requires 
        xp.len() > 0,
        fp.len() == xp.len(),
        x.len() > 0,
        forall|i: int, j: int| 0 <= i < j < xp.len() ==> xp[i] < xp[j],
    ensures 
        result.len() == x.len(),
        forall|k: int| 0 <= k < x.len() ==> (
            (x[k] <= xp[0] ==> result[k] == fp[0]) &&
            (x[k] >= xp[xp.len() - 1] ==> result[k] == fp[fp.len() - 1])
        )
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [fixed while loop invariant syntax by removing braces] */
    let mut result = Vec::new();
    let mut k: usize = 0;
    let xp_len = xp.len();

    while k < x.len()
        decreases x.len() - k
        invariant
            0 <= k <= x.len(),
            result.len() == k,
            xp.len() > 0,
            fp.len() == xp.len(),
            x.len() > 0,
            forall|i: int, j: int| 0 <= i < j < xp.len() ==> xp@[i] < xp@[j],
            forall|l: int| 0 <= l < k ==> (
                (x@[l] <= xp@[0] ==> result@[l] == fp@[0]) &&
                (x@[l] >= xp@[xp.len() - 1] ==> result@[l] == fp@[xp.len() - 1])
            ),
    {
        let x_k = x[k];
        let y_k: i32;

        if x_k <= xp[0] {
            y_k = fp[0];
        } else if x_k >= xp[xp_len - 1] {
            y_k = fp[xp_len - 1];
        } else {
            assert(xp.len() >= 2);
            let i = find_interval_exec(x_k, &xp);

            let x0 = xp[i] as i64;
            let y0 = fp[i] as i64;
            let x1 = xp[i+1] as i64;
            let y1 = fp[i+1] as i64;
            let xk_64 = x_k as i64;

            let dx = x1 - x0;
            assert(dx > 0);
            
            y_k = (y0 + (xk_64 - x0) * (y1 - y0) / dx) as i32;
        }

        result.push(y_k);
        k = k + 1;
    }
    result
}
// </vc-code>

}
fn main() {}