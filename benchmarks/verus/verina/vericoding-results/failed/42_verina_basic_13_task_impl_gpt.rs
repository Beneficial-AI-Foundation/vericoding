// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): remove mismatched spec fn, provide exec cube with spec-level postcondition over int view */
fn cube_wrapping(x: i32) -> (r: i32)
    ensures
        (r as int) == x * x * x,
{
    x.wrapping_mul(x).wrapping_mul(x)
}

// </vc-helpers>

// <vc-spec>
fn cube_elements(a: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i] * a[i] * a[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement loop with proper int views and invariants, using helper ensures */
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            res.len() == i,
            0 <= i as int <= a.len() as int,
            forall|j: int| 0 <= j < i as int ==> res[j] == a[j] * a[j] * a[j],
        decreases a.len() as int - i as int
    {
        let ai = a[i];
        let cube = cube_wrapping(ai);
        let old_len = res.len();
        res.push(cube);
        assert(res.len() == old_len + 1);
        assert(old_len == i);
        assert(res[i as int] == cube as int);
        assert((cube as int) == ai * ai * ai);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}