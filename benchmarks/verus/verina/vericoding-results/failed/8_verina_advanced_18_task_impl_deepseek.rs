// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_digits(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else if n < 10 { 1 } else { 1 + count_digits(n / 10) }
}

spec fn pow_nat(base: nat, exp: nat) -> nat
    decreases exp
{
    if exp == 0 { 
        1 
    } else { 
        base * pow_nat(base, (exp - 1) as nat) 
    }
}

spec fn sum_powers(n: nat, k: nat) -> nat
    decreases n
{
    if n == 0 { 0 } else { pow_nat(n % 10, k) + sum_powers(n / 10, k) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix syntax and add proper proof helpers */
proof fn division_decreases(n: u32)
    requires n > 0
    ensures (n / 10) < n || n < 10
{
    if n >= 10 {
        assert(n / 10 < n);
    }
}

proof fn pow_u32_nonnegative(base: u32, exp: u32)
    requires exp <= 10
    ensures pow_u32(base, exp) >= 0
{
    if exp == 0 {
        assert(pow_u32(base, 0) == 1);
    } else {
        pow_u32_nonnegative(base, exp - 1);
        assert(pow_u32(base, exp) == base * pow_u32(base, exp - 1));
    }
}

proof fn addition_preserves_nonnegativity(a: u32, b: u32)
    requires a >= 0, b >= 0
    ensures a + b >= 0
{
}

spec fn pow_u32(base: u32, exp: u32) -> u32
    decreases exp
{
    if exp == 0 {
        1
    } else {
        base * pow_u32(base, exp - 1)
    }
}
// </vc-helpers>

// <vc-spec>
fn is_armstrong(n: u32) -> (result: bool)
    ensures 
        result == (n as nat == sum_powers(n as nat, count_digits(n as nat))),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix invariant syntax with braces and proper loop implementation */
{
    let k: u32 = if n == 0 {
        1
    } else {
        let mut count = 0;
        let mut temp = n;
        while temp > 0
            invariant count >= 0,
            invariant temp >= 0
        {
            count += 1;
            temp /= 10;
        }
        count
    };
    
    if n < 10 {
        return true;
    }
    
    let mut sum: u32 = 0;
    let mut temp = n;
    
    while temp > 0
        invariant sum >= 0,
        invariant temp >= 0
    {
        let digit = temp % 10;
        let power = pow_u32(digit, k);
        sum += power;
        temp /= 10;
    }
    
    sum == n
}
// </vc-code>

}
fn main() {}