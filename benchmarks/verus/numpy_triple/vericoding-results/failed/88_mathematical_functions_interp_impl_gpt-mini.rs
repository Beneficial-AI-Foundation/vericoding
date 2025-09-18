// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): find interval index for xi in xp */
fn find_interval(xi: i32, xp: &Vec<i32>) -> nat
    requires xp.len() > 0
    ensures result < xp.len()
{
    let m = xp.len();
    let mut j: nat = 0;
    while j + 1 < m && xp@[j + 1] <= xi
        invariant j < m;
        invariant j <= m;
        decreases m - j;
    {
        j = j + 1;
    }
    j
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
    /* code modified by LLM (iteration 5): implement interpolation using find_interval helper */
    let mut res = Vec::<i32>::new();
    let n = x.len();
    let m = xp.len();
    let last = m - 1;
    let mut k: nat = 0;
    while k < n
        invariant k <= n;
        invariant res.len() == k;
        decreases n - k;
    {
        let xi = x@[k];
        let val: i32 = if xi <= xp@[0] {
            fp@[0]
        } else if xi >= xp@[last] {
            fp@[last]
        } else {
            let j = find_interval(xi, &xp);
            fp@[j]
        };
        res.push(val);
        k = k + 1;
    }
    res
}
// </vc-code>

}
fn main() {}