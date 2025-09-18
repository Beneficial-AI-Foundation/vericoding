// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Using vstd bit operation axioms instead of empty proof bodies */
proof fn lemma_left_shift_properties(x: i32, shift: i32)
    requires shift >= 0
    ensures x * pow(2, shift as nat) == (x << shift)
{
    vstd::arithmetic::power::lemma_pow2_strictly_increases(shift as nat);
}

proof fn lemma_pow_positive(base: int, exp: nat)
    requires base > 1
    ensures exp > 0 ==> pow(base, exp) > 1
{
    if exp > 0 {
        vstd::arithmetic::power::lemma_pow_positive(base, exp);
    }
}

proof fn lemma_shift_zero(x: i32)
    ensures (x << 0) == x
{
    assert(pow(2, 0) == 1);
    assert(x * 1 == x);
}

proof fn lemma_shift_preserves_zero(shift: i32)
    requires shift >= 0
    ensures (0 << shift) == 0
{
    assert(0 * pow(2, shift as nat) == 0);
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
    /* code modified by LLM (iteration 5): Fixed bounds checking and added proper proof assertions */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            0 <= i <= x1.len(),
            result.len() == i,
            x1.len() == x2.len(),
            forall|j: int| 0 <= j < i ==> result[j] == x1[j] * pow(2, x2[j] as nat),
        decreases x1.len() - i
    {
        let idx = i as usize;
        assert(idx < x1.len());
        assert(idx < x2.len());
        assert(x2[idx] >= 0);
        
        proof {
            lemma_left_shift_properties(x1[idx], x2[idx]);
        }
        
        let shifted_value = x1[idx] << x2[idx];
        result.push(shifted_value);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}