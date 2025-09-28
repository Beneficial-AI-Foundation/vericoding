// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
#[verus::proof]
fn lemma_right_shift_properties(val1: i32, val2: i32)
    requires
        val2 >= 0,
    ensures {
        let result = val1 >> val2;
        &&& (val1 >= 0 ==> result == val1 / (1i32 << val2))
        &&& (val1 < 0 ==> result == val1 >> val2)
        &&& (val2 == 0 ==> result == val1)
        &&& (val1 > 0 ==> result >= 0)
        &&& (val1 < 0 ==> result <= 0)
        &&& (val1 == 0 ==> result == 0)
    }
{
    if val1 >= 0 {
        let val2_u32 = val2 as u32;
        let shift_amount = val2_u32 % 32;
        assert(shift_amount < 32) by {
            vstd::arithmetic::mod_internals::lemma_mod_range(val2_u32 as int, 32);
        };
        vstd::bitvector::core::lemma_i32_shr_is_div_by_pow2(val1, shift_amount);
    }
}
// </vc-helpers>

// <vc-spec>
fn right_shift(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2.len() ==> x2[i] >= 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            &&& (x1[i] >= 0 ==> result[i] == x1[i] / (1i32 << x2[i]))
            &&& (x1[i] < 0 ==> result[i] == x1[i] >> x2[i])
            &&& (x2[i] == 0 ==> result[i] == x1[i])
            &&& (x1[i] > 0 ==> result[i] >= 0)
            &&& (x1[i] < 0 ==> result[i] <= 0)
            &&& (x1[i] == 0 ==> result[i] == 0)
        }
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            x1.len() == x2.len(),
            forall|j: int| 0 <= j < x2.len() ==> x2[j] >= 0,
            0 <= i <= x1.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> {
                let val1 = x1[k];
                let val2 = x2[k];
                let res = result[k];
                &&& (val1 >= 0 ==> res == val1 / (1i32 << val2))
                &&& (val1 < 0 ==> res == val1 >> val2)
                &&& (val2 == 0 ==> res == val1)
                &&& (val1 > 0 ==> res >= 0)
                &&& (val1 < 0 ==> res <= 0)
                &&& (val1 == 0 ==> res == 0)
            },
        decreases x1.len() - i,
    {
        let val1 = x1[i];
        let val2 = x2[i];

        lemma_right_shift_properties(val1, val2);

        let shifted_val = val1 >> val2;
        result.push(shifted_val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}