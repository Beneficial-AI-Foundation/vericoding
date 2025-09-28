// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed invariants and overflow check logic */
fn power_i8(base: i8, exp: i8) -> (result: i8)
    requires
        base == 0 ==> exp as int >= 0,
    ensures
        exp as int == 0 && base as int != 0 ==> result as int == 1,
        exp as int == 1 ==> result as int == base as int,
        base as int > 1 && exp as int > 1 ==> result as int > base as int,
{
    if exp == 0 {
        if base == 0 {
            0
        } else {
            1
        }
    } else if exp == 1 {
        base
    } else if exp < 0 {
        0
    } else {
        let mut result = 1;
        let mut i = 0;
        while i < exp
            invariant
                i >= 0,
                i <= exp,
                result > 0,
            decreases exp as int - i as int
        {
            if base == 0 {
                result = 0;
                break;
            }
            if result > 127 / base.abs().max(1) {
                result = 127;
                break;
            }
            result = result * base;
            i = i + 1;
        }
        result
    }
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
{
    /* code modified by LLM (iteration 5): fixed array indexing type errors */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            i <= x1.len(),
            result.len() == i,
            x1.len() == x2.len(),
            forall|j: int| 0 <= j < i ==> {
                (x2@[j] as int == 0 && x1@[j] as int != 0 ==> result@[j] as int == 1) &&
                (x2@[j] as int == 1 ==> result@[j] as int == x1@[j] as int) &&
                (x1@[j] as int > 1 && x2@[j] as int > 1 ==> result@[j] as int > x1@[j] as int)
            },
        decreases x1.len() - i
    {
        proof {
            assert(0 <= i < x1@.len());
            assert(x1@[i as int] == 0 ==> x2@[i as int] as int >= 0);
        }
        let power_result = power_i8(x1[i], x2[i]);
        result.push(power_result);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}