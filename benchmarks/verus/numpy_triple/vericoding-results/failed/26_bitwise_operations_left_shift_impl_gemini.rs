// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_mul_by_pow2_gt(x: int, n: nat)
    requires x > 0, n > 0
    ensures x * pow(2, n) > x
{
    vstd::arithmetic::power::lemma_pow_gt_one(2, n);
    vstd::arithmetic::mul_internals::lemma_mul_inequality(x, pow(2, n), 1);
}

proof fn lemma_mul_by_pow2_lt(x: int, n: nat)
    requires x < 0, n > 0
    ensures x * pow(2, n) < x
{
    vstd::arithmetic::power::lemma_pow_gt_one(2, n);
    vstd::arithmetic::mul_internals::lemma_mul_inequality_flip(x, pow(2, n), 1);
}
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
    let mut result: Vec<i32> = Vec::new_with_len(x1.len());
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            x1.len() == x2.len(),
            forall|j: int| 0 <= j < x2.len() ==> x2[j] >= 0,
            i <= x1.len(),
            result.len() == x1.len(),
            forall|j: int| 0 <= j < i ==> result.view()[j] == x1.view()[j] * pow(2, x2.view()[j] as nat),
    {
        let val = x1[i] << (x2[i] as u32);
        result.set(i, val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}