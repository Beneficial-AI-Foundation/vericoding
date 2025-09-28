// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type mismatch with int indexing */
fn find_interval(x_val: i32, xp: &Vec<i32>) -> usize
    requires
        xp.len() > 0,
        forall|i: int, j: int| 0 <= i < j < xp.len() ==> xp[i] < xp[j],
    ensures
        find_interval(x_val, xp) < xp.len(),
{
    if x_val < xp[0] {
        0
    } else if x_val >= xp[xp.len() - 1] {
        xp.len() - 1
    } else {
        let mut i: usize = 0;
        while i + 1 < xp.len() && x_val >= xp[i + 1]
            invariant
                i < xp.len() - 1,
                x_val >= xp[i as int],
            decreases xp.len() - i
        {
            i = i + 1;
        }
        i + 1
    }
}

fn linear_interp(x_val: i32, x0: i32, x1: i32, y0: i32, y1: i32) -> i32
    requires
        x0 <= x_val <= x1,
        x0 < x1,
{
    if x_val == x0 {
        y0
    } else if x_val == x1 {
        y1
    } else {
        y0 + ((y1 - y0) * (x_val - x0)) / (x1 - x0)
    }
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
    /* code modified by LLM (iteration 5): fixed type mismatch with int indexing */
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> (
                (x[k] <= xp[0] ==> result[k] == fp[0]) &&
                (x[k] >= xp[xp.len() - 1] ==> result[k] == fp[fp.len() - 1])
            ),
        decreases x.len() - i
    {
        let x_val = x[i as int];
        
        let interp_val = if x_val <= xp[0] {
            fp[0]
        } else if x_val >= xp[xp.len() - 1] {
            fp[fp.len() - 1]
        } else {
            let idx = find_interval(x_val, &xp);
            linear_interp(x_val, xp[idx as int - 1], xp[idx as int], fp[idx as int - 1], fp[idx as int])
        };
        
        result.push(interp_val);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}