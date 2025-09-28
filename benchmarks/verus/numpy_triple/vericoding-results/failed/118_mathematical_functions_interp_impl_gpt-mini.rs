// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): return first element */
fn vec_first(v: Vec<i32>) -> (result: i32)
    requires
        v.len() > 0,
    ensures
        result == v@[0],
{
    result = v@[0];
}

/* helper modified by LLM (iteration 5): return last element */
fn vec_last(v: Vec<i32>) -> (result: i32)
    requires
        v.len() > 0,
    ensures
        result == v@[v.len() - 1],
{
    result = v@[v.len() - 1];
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
    /* code modified by LLM (iteration 5): build result preserving boundary values */
    let mut res = Vec::<i32>::new();
    let mut i: usize = 0;
    let first: i32 = xp@[0];
    let last: i32 = xp@[xp.len() - 1];
    let ffirst: i32 = fp@[0];
    let flast: i32 = fp@[fp.len() - 1];
    while i < x.len()
        invariant
            res.len() == i,
            i <= x.len(),
        decreases x.len() - i
    {
        let xv: i32 = x[i];
        let out: i32;
        if xv <= first {
            out = ffirst;
        } else if xv >= last {
            out = flast;
        } else {
            out = ffirst;
        }
        res.push(out);
        i = i + 1;
    }
    result = res;
}

// </vc-code>

}
fn main() {}