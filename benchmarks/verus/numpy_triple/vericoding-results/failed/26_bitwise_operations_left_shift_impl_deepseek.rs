// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_pow_positive(base: int, exponent: nat)
    decreases exponent
    ensures
        base > 0 ==> pow(base, exponent) > 0,
        base < 0 ==> (exponent % 2 == 0) ==> pow(base, exponent) > 0,
        base < 0 ==> (exponent % 2 == 1) ==> pow(base, exponent) < 0,
{
    if exponent == 0 {
        assert(pow(base, 0) == 1) by (compute);
    } else {
        let prev_exponent: nat = (exponent - 1) as nat;
        lemma_pow_positive(base, prev_exponent);
        if base > 0 {
            assert(pow(base, exponent) == base * pow(base, prev_exponent)) by (compute);
            assert(pow(base, exponent) > 0);
        } else if base < 0 {
            assert(pow(base, exponent) == base * pow(base, prev_exponent)) by (compute);
            if exponent % 2 == 0 {
                assert(pow(base, prev_exponent) < 0);
                assert(pow(base, exponent) > 0);
            } else {
                assert(pow(base, prev_exponent) > 0);
                assert(pow(base, exponent) < 0);
            }
        }
    }
}

spec fn cast_i32_to_nat(x: i32) -> nat
    recommends x >= 0
{
    x as nat
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
    /* code modified by LLM (iteration 5): Fixed compilation error by ensuring 1i32 is cast to i64 before bit shifting */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    while i < x1.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == x1@[j] * pow(2, cast_i32_to_nat(x2@[j])),
            forall|j: int| 0 <= j < i && x2@[j] == 0 ==> result@[j] == x1@[j],
            forall|j: int| 0 <= j < i && x1@[j] == 0 ==> result@[j] == 0,
            forall|j: int| 0 <= j < i && x1@[j] > 0 && x2@[j] > 0 ==> result@[j] > x1@[j],
            forall|j: int| 0 <= j < i && x1@[j] < 0 && x2@[j] > 0 ==> result@[j] < x1@[j],
        decreases x1.len() - i,
    {
        let x1_val = x1[i];
        let x2_val = x2[i];
        
        proof {
            let exponent: nat = cast_i32_to_nat(x2_val);
            lemma_pow_positive(2, exponent);
        }
        
        let shift_amount = ((1i64) << x2_val) as i32;
        let value = x1_val * shift_amount;
        
        result.push(value);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}