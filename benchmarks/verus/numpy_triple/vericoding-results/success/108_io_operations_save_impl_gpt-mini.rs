// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): return length as usize (runtime-safe) */
fn vec_len(v: &Vec<f32>) -> usize {
    v.len()
}
// </vc-helpers>

// <vc-spec>
fn save(file: String, arr: Vec<f32>, allow_pickle: bool) -> (result: ())
    ensures result == (),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): compute length as usize and no-op save */
    let _len: usize = vec_len(&arr);
    if allow_pickle {
        let _ = _len;
    } else {
        let _ = _len;
    }
}
// </vc-code>

}
fn main() {}