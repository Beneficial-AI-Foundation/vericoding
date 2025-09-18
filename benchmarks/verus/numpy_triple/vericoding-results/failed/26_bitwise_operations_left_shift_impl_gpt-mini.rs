// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): returns 2^e */
spec fn shift_factor(e: nat) -> nat { pow(2, e) }
// </vc-helpers>

// <vc-spec>
fn left_shift(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2.len() ==> x2[i] >= 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == x1[i] * pow(2, x2[i] as nat),
        forall|i: int| 0 <= i < result.len() && x2[i] == 0 ==> result[i] == x1[i],
        forall|i: int| 0 <= i < result.len() && x1[i] == 0 ==> result[i] == 0,
        forall|i: int| 0 <= i < result.len() && x1[i] > 0 && x2[i] > 0 ==> result[i] > x1[i],
        forall|i: int| 0 <= i < result.len() && x1[i] < 0 && x2[i] > 0 ==> result[i] < x1[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement left_shift using nat indices and maintained invariants */
    let mut res: Vec<i32> = Vec::new();
    let n: nat = x1.len() as nat;
    let mut i: nat = 0;
    while i < n
        invariant i <= n
        invariant res.len() == i
        invariant forall|j: nat| j < i ==> res@[j] == x1@[j] * (shift_factor(x2@[j] as nat) as i32)
        decreases n - i
    {
        let factor_nat: nat = shift_factor(x2@[i] as nat);
        let factor: i32 = factor_nat as i32;
        let val: i32 = x1@[i] * factor;
        res.push(val);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}