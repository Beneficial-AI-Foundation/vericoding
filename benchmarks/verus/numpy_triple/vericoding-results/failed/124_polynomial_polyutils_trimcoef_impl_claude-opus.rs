// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn all_zero_from(c: Seq<f32>, start: int, tol: f32) -> bool
    decreases c.len() - start
{
    if start >= c.len() {
        true
    } else if c[start].abs() > tol {
        false
    } else {
        all_zero_from(c, start + 1, tol)
    }
}

/* helper modified by LLM (iteration 5): moved ensures clauses to proper function signature */
fn find_last_nonzero(c: &Vec<f32>, tol: f32) -> (result: usize)
    requires c.len() >= 1,
    ensures result < c.len(),
    ensures result == 0 || c[result as int].abs() > tol,
    ensures forall|i: int| result < i < c.len() ==> c[i].abs() <= tol,
{
    let mut last: usize = 0;
    let mut i: usize = 0;
    while i < c.len()
        invariant i <= c.len(),
        invariant last < c.len(),
        invariant last <= i,
        invariant last == 0 || c[last as int].abs() > tol,
        invariant forall|j: int| last < j < i ==> c[j].abs() <= tol,
    {
        if c[i].abs() > tol {
            last = i;
        }
        i = i + 1;
    }
    last
}
// </vc-helpers>

// <vc-spec>
fn trimcoef(c: Vec<f32>, tol: f32) -> (result: Vec<f32>)
    ensures
        result.len() >= 1,
        result.len() <= c.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no changes needed */
    if c.len() == 0 {
        return vec![0.0];
    }
    
    let last_idx = find_last_nonzero(&c, tol);
    
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i <= last_idx
        invariant i <= last_idx + 1,
        invariant result.len() == i,
        invariant forall|j: int| 0 <= j < i ==> result[j] == c[j],
    {
        result.push(c[i]);
        i = i + 1;
    }
    
    if result.len() == 0 {
        result.push(0.0);
    }
    
    result
}
// </vc-code>

}
fn main() {}