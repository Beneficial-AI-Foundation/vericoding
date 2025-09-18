// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): or_zero_i32 proves x | 0 == x */
proof fn or_zero_i32(x: i32) ensures x | 0 == x {
    assert(x | 0 == x);
}

/* helper modified by LLM (iteration 5): or_all_ones_i32 proves x | -1 == -1 for i32 */
proof fn or_all_ones_i32(x: i32) ensures x | -1i32 == -1i32 {
    assert(x | -1i32 == -1i32);
}
// </vc-helpers>

// <vc-spec>
spec fn bitwise_or_int(x: i32, y: i32) -> i32 {
    x
}

spec fn bitwise_and_int(x: i32, y: i32) -> i32 {
    x
}

spec fn bitwise_or_vec(x: Seq<i32>, y: Seq<i32>) -> Seq<i32>
    recommends x.len() == y.len()
{
    Seq::new(x.len(), |i: int| x[i])
}

fn bitwise_or_fn(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == bitwise_or_int(x1[i], x2[i]),
        forall|i: int| 0 <= i < result.len() && x2[i] == 0 ==> result[i] == x1[i],
        forall|i: int| 0 <= i < result.len() && x1[i] == 0 ==> result[i] == x2[i],
        forall|i: int| 0 <= i < result.len() && (x1[i] == -1i32 || x2[i] == -1i32) ==> result[i] == -1i32,
        result@ == bitwise_or_vec(x1@, x2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): element-wise bitwise OR implemented with loop */
    let mut result: Vec<i32> = Vec::new();
    for idx in 0..x1.len() {
        let a: i32 = x1[idx];
        let b: i32 = x2[idx];
        let r: i32 = a | b;
        result.push(r);
    }
    result
}
// </vc-code>

}
fn main() {}