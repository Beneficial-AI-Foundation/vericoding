// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn find_interval(x_val: i32, xp: Vec<i32>) -> (i: nat)
    requires
        xp.len() > 0,
        forall|i: int, j: int| 0 <= i < j < xp.len() ==> xp[i] < xp[j]
    ensures
        i < xp.len(),
        i == 0 ==> x_val <= xp[0],
        i == xp.len() - 1 ==> x_val >= xp[xp.len() - 1],
        0 < i < xp.len() - 1 ==> xp[i - 1] < x_val <= xp[i]
{
    if x_val <= xp[0] {
        0
    } else if x_val >= xp[xp.len() - 1] {
        (xp.len() - 1) as nat
    } else {
        choose|i: nat| 0 < i < xp.len() && xp[i - 1] < x_val <= xp[i]
    }
}

fn find_interval_exec(x_val: i32, xp: &Vec<i32>) -> (i: usize)
    requires
        xp.len() > 0,
        forall|i: int, j: int| 0 <= i < j < xp.len() ==> xp[i] < xp[j]
    ensures
        i < xp.len(),
        i == 0 ==> x_val <= xp[0],
        i == xp.len() - 1 ==> x_val >= xp[xp.len() - 1],
        0 < i < xp.len() - 1 ==> xp[i as int - 1] < x_val <= xp[i as int]
{
    if x_val <= xp[0] {
        return 0;
    }
    if x_val >= xp[xp.len() - 1] {
        return xp.len() - 1;
    }
    
    let mut left: usize = 0;
    let mut right: usize = xp.len() - 1;
    
    while left + 1 < right
        invariant
            0 <= left < right < xp.len(),
            xp[left as int] < x_val,
            x_val <= xp[right as int]
    {
        let mid = left + (right - left) / 2;
        if x_val <= xp[mid] {
            right = mid;
        } else {
            left = mid;
        }
    }
    
    right
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
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> (
                (x[k] <= xp[0] ==> result[k] == fp[0]) &&
                (x[k] >= xp[xp.len() - 1] ==> result[k] == fp[fp.len() - 1])
            )
    {
        let x_val = x[i];
        let idx = find_interval_exec(x_val, &xp);
        
        let y_val = if idx == 0 {
            fp[0]
        } else if idx == xp.len() - 1 {
            fp[fp.len() - 1]
        } else {
            let x1 = xp[idx - 1];
            let x2 = xp[idx];
            let y1 = fp[idx - 1];
            let y2 = fp[idx];
            y1 + ((x_val - x1) * (y2 - y1)) / (x2 - x1)
        };
        
        result.push(y_val);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}