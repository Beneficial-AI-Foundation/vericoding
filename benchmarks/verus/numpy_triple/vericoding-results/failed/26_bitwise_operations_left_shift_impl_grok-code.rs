// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes needed */
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
    /* code modified by LLM (iteration 5): added loop labels to associate invariants with loops to fix compilation error */
    let mut result = Vec::new();
    'outer: for i in 0..x1.len()
        invariant(x1.len() == x2.len())
        invariant(result.len() == i)
        invariant(forall|j: int| 0 <= j < i ==> result.index(j) == x1.index(j) * pow(2, x2.index(j) as nat))
    {
        proof { assert(i < x1.len()); assert(i < x2.len()); }
        let mut val = x1[i];
        let mut exp = x2[i];
        'inner: while exp > 0
            decreases exp
            invariant(val == x1.index(i) * pow(2, (x2.index(i) - exp) as nat))
        {
            val = val.wrapping_mul(2);
            exp = exp - 1;
        }
        result.push(val);
    }
    result
}
// </vc-code>

}
fn main() {}