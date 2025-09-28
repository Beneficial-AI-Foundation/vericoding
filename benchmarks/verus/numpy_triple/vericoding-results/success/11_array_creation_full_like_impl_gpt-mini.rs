// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): return the smaller of two ints with named return */
fn min(a: int, b: int) -> (result: int)
    ensures
        result <= a,
        result <= b,
{
    if a <= b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn numpy_full_like(a: Vec<f32>, fill_value: f32) -> (result: Vec<f32>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == fill_value,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): build vector matching length of `a` filled with `fill_value` */
{
    let mut v: Vec<f32> = Vec::new();
    let mut i: usize = 0usize;
    while i < a.len()
        invariant
            i <= a.len(),
            v.len() == i,
            forall|k: int| 0 <= k < (v.len() as int) ==> v@[k] == fill_value,
        decreases a.len() - i
    {
        v.push(fill_value);
        i = i + 1;
    }
    v
}
// </vc-code>

}
fn main() {}