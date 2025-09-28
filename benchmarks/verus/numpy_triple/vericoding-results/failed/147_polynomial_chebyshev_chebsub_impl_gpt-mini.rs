// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): trivial proof helper to satisfy placeholder */
proof fn chebsub_helper_noop() {
}

// </vc-helpers>

// <vc-spec>
fn chebsub(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    requires c1.len() == c2.len(),
    ensures 
        result.len() == c1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == c1[i] as int - c2[i] as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): element-wise subtraction using int index and usize cast for safe vector access */
    let n: int = c1.len() as int;
    let mut res: Vec<i8> = Vec::new();
    let mut i: int = 0;
    while i < n
        invariant
            0 <= i,
            res.len() as int == i,
            forall|j: int| 0 <= j && j < i ==> res@[j] as int == c1@[j] as int - c2@[j] as int,
        decreases n - i
    {
        let idx: usize = i as usize;
        let d: i8 = c1[idx] - c2[idx];
        res.push(d);
        i = i + 1;
    }
    res
}
// </vc-code>


}
fn main() {}