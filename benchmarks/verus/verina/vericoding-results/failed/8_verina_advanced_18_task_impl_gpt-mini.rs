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
/* helper modified by LLM (iteration 5): u32 helper functions with return types fixed and unnecessary requires removed */

fn count_digits_u32(m: u32) -> u32
    ensures result as nat == count_digits(m as nat)
{
    if m == 0 {
        1u32
    } else {
        let mut n = m / 10;
        let mut cnt: u32 = 1;
        while n > 0
            invariant cnt as nat + count_digits(n as nat) == count_digits(m as nat)
            decreases n as nat
        {
            cnt = cnt + 1;
            n = n / 10;
        }
        cnt
    }
}

fn pow_u32(base: u32, exp: u32) -> u32
    ensures result as nat == pow_nat(base as nat, exp as nat)
{
    let mut r: u32 = 1;
    let mut i: u32 = 0;
    while i < exp
        invariant r as nat == pow_nat(base as nat, i as nat)
        decreases (exp - i) as nat
    {
        r = r * base;
        i = i + 1;
    }
    r
}

fn sum_powers_u32(m: u32, k: u32) -> u32
    ensures result as nat == sum_powers(m as nat, k as nat)
{
    if m == 0 {
        0u32
    } else {
        let mut n = m;
        let mut acc: u32 = 0;
        while n > 0
            invariant acc as nat + sum_powers(n as nat, k as nat) == sum_powers(m as nat, k as nat)
            decreases n as nat
        {
            let d = n % 10;
            let p = pow_u32(d, k);
            acc = acc + p;
            n = n / 10;
        }
        acc
    }
}

// </vc-helpers>

// <vc-spec>
fn is_armstrong(n: u32) -> (result: bool)
    ensures 
        result == (n as nat == sum_powers(n as nat, count_digits(n as nat))),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute digit count and sum and compare */
    let k = count_digits_u32(n);
    let sum = sum_powers_u32(n, k);
    proof {
        assert(k as nat == count_digits(n as nat));
        assert(sum as nat == sum_powers(n as nat, k as nat));
        assert(sum as nat == sum_powers(n as nat, count_digits(n as nat)));
    }
    n == sum
}

// </vc-code>

}
fn main() {}