// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed overflow handling and invariant maintenance */
fn power_i8(base: i8, exp: i8) -> (result: i8)
    ensures
        (exp == 0 && base != 0 ==> result == 1) &&
        (exp == 1 ==> result == base) &&
        (base > 1 && exp > 0 ==> result > base)
{
    if exp == 0 {
        1
    } else if exp == 1 {
        base
    } else if exp < 0 {
        if base == 1 || base == -1 {
            if exp % 2 == 0 {
                1
            } else {
                base
            }
        } else {
            0
        }
    } else {
        if base == 0 {
            0
        } else if base == 1 {
            1
        } else if base == -1 {
            if exp % 2 == 0 {
                1
            } else {
                -1
            }
        } else {
            let mut res = base;
            let mut count = 1;
            while count < exp
                invariant
                    count >= 1,
                    count <= exp,
                    res >= base || count == 1,
                decreases exp - count
            {
                match res.checked_mul(base) {
                    Some(n) => res = n,
                    None => {
                        if base > 0 {
                            res = i8::MAX;
                        } else {
                            res = base;
                        }
                        break;
                    }
                }
                count += 1;
            }
            res
        }
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
/* code modified by LLM (iteration 5): no changes needed, relies on fixed helper */
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            0 <= i <= x1.len(),
            result.len() == i,
            x1.len() == x2.len(),
        decreases x1.len() - i
    {
        let x1_i = x1[i];
        let x2_i = x2[i];
        result.push(power_i8(x1_i, x2_i));
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}