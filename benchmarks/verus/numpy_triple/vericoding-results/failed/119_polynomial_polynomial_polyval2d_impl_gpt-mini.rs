// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): integer min helper */
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn polyval2d(x: Vec<f32>, y: Vec<f32>, c: Vec<Vec<f32>>) -> (result: Vec<f32>)
    requires 
        x.len() == y.len(),
        x.len() > 0,
        c.len() > 0,
        forall|i: int| #![trigger c[i]] 0 <= i < c.len() ==> c[i].len() > 0,
        forall|i: int| #![trigger c[i]] 0 <= i < c.len() ==> c[i].len() == c[0].len(),
    ensures
        result.len() == x.len(),
        true, // 2D polynomial evaluation results exist (simplified)

        (c.len() == 1 && c[0].len() == 1) ==> 
            (forall|k: int| 0 <= k < result.len() ==> result[k] == c[0][0]),

        (forall|i: int, j: int| 0 <= i < c.len() && 0 <= j < c[i].len() ==> c[i][j] == 0.0f32) ==> 
            (forall|k: int| 0 <= k < result.len() ==> result[k] == 0.0f32),

        forall|k: int| 0 <= k < result.len() && x[k] == 0.0f32 && y[k] == 0.0f32 ==> 
            result[k] == c[0][0],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement polyval2d evaluation with invariants and decreases */
    let n = x.len();
    let m = c.len();
    let p = c[0].len();

    let mut all_zero: bool = true;
    let mut ii: usize = 0;
    while ii < m
        invariant ii <= m
        decreases m - ii
    {
        let mut jj: usize = 0;
        while jj < p
            invariant jj <= p
            decreases p - jj
        {
            if c[ii][jj] != 0.0f32 {
                all_zero = false;
            }
            jj += 1;
        }
        ii += 1;
    }

    let single = m == 1 && p == 1;

    let mut result: Vec<f32> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant k <= n, result.len() == k
        decreases n - k
    {
        let xk = x[k];
        let yk = y[k];

        if single {
            result.push(c[0][0]);
        } else if all_zero {
            result.push(0.0f32);
        } else if xk == 0.0f32 && yk == 0.0f32 {
            result.push(c[0][0]);
        } else {
            let mut sum: f32 = 0.0f32;
            let mut i: usize = 0;
            let mut xpow: f32 = 1.0f32;
            while i < m
                invariant i <= m
                decreases m - i
            {
                let mut j: usize = 0;
                let mut ypow: f32 = 1.0f32;
                while j < p
                    invariant j <= p
                    decreases p - j
                {
                    sum = sum + c[i][j] * xpow * ypow;
                    ypow = ypow * yk;
                    j += 1;
                }
                xpow = xpow * xk;
                i += 1;
            }
            result.push(sum);
        }

        k += 1;
    }

    result
}
// </vc-code>

}
fn main() {}