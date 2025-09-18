// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed f32 comparison using raw operators and return statement */
spec fn find_last_nonzero(c: &Vec<f32>, tol: f32) -> (idx: int)
    requires
        c.len() >= 1,
        tol >= 0.0f32,
    ensures
        idx >= -1,
        idx <= (c.len() as int) - 1,
        forall|i: int| idx < i && i < c.len() as int ==> c@[i] <= tol,
        idx >= 0 ==> c@[idx] > tol
{
    if (c.len() as int) == 0 {
        -1
    } else {
        let mut ghost_i: int = (c.len() as int) - 1;
        while ghost_i >= 0
            invariant
                -1 <= ghost_i <= (c.len() as int) - 1,
                forall|j: int| ghost_i < j && j < c.len() as int ==> c@[j] <= tol,
        {
            if c@[ghost_i] > tol {
                return ghost_i;
            }
            ghost_i = ghost_i - 1;
        }
        -1
    }
}
// </vc-helpers>

// <vc-spec>
fn trimcoef(c: Vec<f32>, tol: f32) -> (result: Vec<f32>)
    ensures
        result.len() >= 1,
        result.len() <= c.len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type casting and vector access syntax */
{
    proof {
        let ghost_last_idx = find_last_nonzero(&c, tol);
        assert(ghost_last_idx >= -1 && ghost_last_idx <= (c.len() as int) - 1);
    }
    
    let mut last_nonzero_idx: isize = -1;
    let len = c.len() as isize;
    let mut i: isize = len - 1;
    while i >= 0
        invariant
            -1 <= i <= len - 1,
            last_nonzero_idx >= -1,
            last_nonzero_idx <= len - 1,
    {
        if c[i as usize] > tol {
            last_nonzero_idx = i;
            break;
        }
        i = i - 1;
    }
    
    if last_nonzero_idx >= 0 {
        let end = (last_nonzero_idx + 1) as usize;
        let mut result = Vec::new();
        let mut i: usize = 0;
        while i < end
            invariant
                i <= end,
                result.len() == i,
                forall|j: int| 0 <= j < i ==> result@[j] == c@[j],
        {
            result.push(c[i]);
            i = i + 1;
        }
        result
    } else {
        vec![0.0]
    }
}
// </vc-code>

}
fn main() {}