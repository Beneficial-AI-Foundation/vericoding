// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): recursive constructor for bitwise-and vector */
fn build_and(x1: Vec<i32>, x2: Vec<i32>, i: int) -> (result: Vec<i32>)
    requires x1.len() == x2.len(),
    requires 0 <= i && i <= x1.len(),
    requires forall|k: int| 0 <= k < x1.len() ==> x1[@k] >= 0 && x2[@k] >= 0,
    decreases x1.len() - i,
    ensures result.len() == x1.len() - i,
    ensures forall|k: int| 0 <= k < result.len() ==> result[@k] == x1[@(i + k)] & x2[@(i + k)]
{
    if i == x1.len() {
        Vec::new()
    } else {
        let a: i32 = x1[@i];
        let b: i32 = x2[@i];
        let c: i32 = a & b;
        let mut tail = build_and(x1, x2, i + 1);
        let mut v: Vec<i32> = Vec::new();
        v.push(c);
        v.append(tail);
        v
    }
}
// </vc-helpers>

// <vc-spec>
fn bitwise_and(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x1.len() ==> x1[i] >= 0,
        forall|i: int| 0 <= i < x2.len() ==> x2[i] >= 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] & x2[i]),
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,
        forall|i: int| 0 <= i < result.len() ==> result[i] <= x1[i],
        forall|i: int| 0 <= i < result.len() ==> result[i] <= x2[i],
        forall|i: int| 0 <= i < result.len() ==> (result[i] == 0 <==> (x1[i] == 0 || x2[i] == 0)),
        forall|i: int| 0 <= i < result.len() ==> (x1[i] == x2[i] ==> result[i] == x1[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): construct result via recursive helper */
    let res = build_and(x1, x2, 0);
    res
}
// </vc-code>

}
fn main() {}