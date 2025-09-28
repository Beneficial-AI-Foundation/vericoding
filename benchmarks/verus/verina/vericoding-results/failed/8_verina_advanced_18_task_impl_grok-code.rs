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
/* helper modified by LLM (iteration 2): added executable functions for digit count, power, and sum of powers with verification ensures */
proof fn count_exec_inv(m: u32, orig: u32, count: u32)
    ensures
        count as nat + count_digits(m as nat) == count_digits(orig as nat)
    decreases m
{
    if m == 0 {

    } else {
        count_exec_inv(m / 10, orig, count + 1)
    }
}

fn count_digits_exec(n: u32) -> (count: u32)
    ensures
        count as nat == count_digits(n as nat)
{
    if n == 0 {
        return 1;
    }
    let mut m = n;
    let mut c = 0;
    while m > 0
        invariant
            c as nat + count_digits(m as nat) == count_digits(n as nat)
        decreases m
    {
        c += 1;
        m /= 10;
    }
    c
}

fn pow_exec(base: u32, exp: u32) -> u64
    decreases exp
    ensures
        pow_exec(base, exp) == pow_nat(base as nat, exp as nat)
{
    if exp == 0 {
        1
    } else {
        (base as u64) * pow_exec(base, exp - 1)
    }
}

fn sum_powers_exec(n: u32, k: u32) -> u64
    decreases n
    ensures
        sum_powers_exec(n, k) == sum_powers(n as nat, k as nat)
{
    if n == 0 {
        0
    } else {
        pow_exec(n % 10, k) + sum_powers_exec(n / 10, k)
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
/* code modified by LLM (iteration 2): calculate digit count and sum of digits raised to the power of digit count, then check equality for Armstrong number */
    let digit_count = count_digits_exec(n);
    let sum = sum_powers_exec(n, digit_count);
    n as u64 == sum
}
// </vc-code>

}
fn main() {}