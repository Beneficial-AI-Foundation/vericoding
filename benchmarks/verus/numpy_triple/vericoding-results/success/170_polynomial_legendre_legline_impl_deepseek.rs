// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

fn min(a: int, b: int) -> int {
    if a < b {
        a
    } else {
        b
    }
}

spec fn abs(x: int) -> int {
    if x >= 0 {
        x
    } else {
        -x
    }
}

proof fn lemma_vec_indexing<T>(v: Vec<T>, i: int)
    requires
        0 <= i < v.len(),
    ensures
        v@[i] === v[i]
{
    // Vec indexing lemma
}

// </vc-helpers>

// <vc-spec>
fn legline(off: f32, scl: f32) -> (result: Vec<f32>)
    ensures
        result.len() == 2,
        result[0] == off,
        result[1] == scl
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    result.push(off);
    result.push(scl);
    proof {
        lemma_vec_indexing(result, 0);
        lemma_vec_indexing(result, 1);
    }
    result
}
// </vc-code>

}
fn main() {}