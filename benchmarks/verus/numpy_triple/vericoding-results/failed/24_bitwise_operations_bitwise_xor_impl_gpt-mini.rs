// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): returns length of Vec<i32> as int */
spec fn int_of_len(v: Vec<i32>) -> int { v.len() }
// </vc-helpers>

// <vc-spec>
fn bitwise_xor(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x1.len() ==> x1[i] >= 0,
        forall|i: int| 0 <= i < x2.len() ==> x2[i] >= 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] ^ x2[i]),
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,
        forall|i: int| 0 <= i < result.len() && x1[i] == 0 ==> result[i] == x2[i],
        forall|i: int| 0 <= i < result.len() && x2[i] == 0 ==> result[i] == x1[i],
        forall|i: int| 0 <= i < result.len() && x1[i] == x2[i] ==> result[i] == 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterative xor building result with invariants using int_of_len helper */
    let mut res: Vec<i32> = Vec::new();
    let n: int = x1.len();
    let mut i: int = 0;
    while i < n
        invariant 0 <= i && i <= n,
        invariant int_of_len(res) == i,
        invariant forall|j: int| 0 <= j && j < i ==> res@[j] == (x1@[j] ^ x2@[j]),
        invariant forall|j: int| 0 <= j && j < i ==> res@[j] >= 0,
        decreases n - i
    {
        let v1: i32 = x1[i];
        let v2: i32 = x2[i];
        let v: i32 = v1 ^ v2;
        res.push(v);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}