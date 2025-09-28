// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn power(base: int, exp: nat) -> int
    decreases exp
{
    if exp == 0 {
        1
    } else {
        base * power(base, (exp - 1) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix loop variable to u8 to avoid signed overflow when incrementing from 127 */
fn compute_mod2_pow(exp: i8, modulus: i8) -> (result: i8)
    requires
        0 <= exp,
        0 < modulus,
    ensures
        0 <= result,
        result < modulus,
        result as int == power(2, exp as nat) % (modulus as int),
{
    let init: i32 = 1 % (modulus as i32);
    let mut current_result: i32 = init;
    let mut i: u8 = 0;
    let exp_u8 = exp as u8;
    while i < exp_u8
        invariant
            (i as int) <= (exp as int),
            0 <= current_result < (modulus as i32),
            current_result as int == power(2, i as nat) % (modulus as int),
        decreases (exp_u8 - i) as nat
    {
        let temp: i32 = (current_result * 2) % (modulus as i32);
        current_result = temp;
        i = i + 1;
    }
    current_result as i8
}
// </vc-helpers>

// <vc-spec>
fn modp(n: i8, p: i8) -> (result: i8)
    requires 
        n >= 0 && p > 0,
    ensures 
        result >= 0 && result < p,
        result as int == power(2, n as nat) % (p as int),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): call the fixed helper function */
{
    compute_mod2_pow(n, p)
}
// </vc-code>


}

fn main() {}