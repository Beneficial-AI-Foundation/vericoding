// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed predicate syntax with func keyword and proper types */

fn power_base_case(base: i8, exponent: i8) -> (result: i8)
    requires
        exponent == 0 ==> base != 0,
        exponent == 1,
    ensures
        exponent == 0 ==> result == 1,
        exponent == 1 ==> result == base,
{
    if exponent == 0 {
        1
    } else {
        base
    }
}

fn power_recursive(base: i8, exponent: i8) -> (result: i8)
    requires
        base > 1,
        exponent > 0,
        exponent <= 5,
    ensures
        result > base,
{
    if exponent == 1 {
        base
    } else {
        let intermediate = power_recursive(base, exponent - 1);
        base * intermediate
    }
}

fn is_nonnegative_exponent_when_zero_base(base: i8, exponent: i8) -> bool {
    base == 0 ==> exponent >= 0
}

lemma zero_base_nonnegative_exponent_proof(base: i8, exponent: i8)
    requires
        base == 0,
    ensures
        exponent >= 0,
{
}
// </vc-helpers>

// <vc-spec>
fn numpy_power(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x1@.len() ==> {
            (x1[i] == 0 ==> x2[i] as int >= 0)
        },
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result@.len() ==> {
            (x2[i] as int == 0 && x1[i] as int != 0 ==> result[i] as int == 1) &&
            (x2[i] as int == 1 ==> result[i] as int == x1[i] as int) &&
            (x1[i] as int > 1 && x2[i] as int > 0 ==> result[i] as int > x1[i] as int)
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error in helper predicate */
{
    let mut result = Vec::new();
    let mut idx: usize = 0;
    
    while idx < x1.len()
        invariant
            result.len() == idx,
            forall|i: int| 0 <= i < idx ==> {
                let base_val = x1@[i] as int;
                let exp_val = x2@[i] as int;
                (exp_val == 0 && base_val != 0 ==> result@[i] as int == 1) &&
                (exp_val == 1 ==> result@[i] as int == base_val) &&
                (base_val > 1 && exp_val > 0 ==> result@[i] as int > base_val) &&
                (base_val == 0 && exp_val >= 0 ==> result@[i] as int == 0)
            },
        decreases x1.len() - idx,
    {
        let base = x1[idx];
        let exponent = x2[idx];
        let value = 
            if exponent == 0 && base != 0 {
                1
            } else if exponent == 1 {
                base
            } else if base > 1 && exponent > 0 {
                power_recursive(base, exponent)
            } else if base == 0 && exponent >= 0 {
                0
            } else {
                base
            };
        result.push(value);
        idx = idx + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}