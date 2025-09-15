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
/* helper modified by LLM (iteration 5): Changed return types from nat to u32, adjusted ensures to cast u32 to nat, and modified body to avoid casting base to nat in executable code */
fn exec_count_digits(n: u32) -> (result: u32)
    ensures result as nat == count_digits(n as nat)
    decreases n
{
    if n == 0 {
        1
    } else if n < 10 {
        1
    } else {
        1 + exec_count_digits(n / 10)
    }
}

fn exec_pow(base: u32, exp: u32) -> (result: u32)
    ensures result as nat == pow_nat(base as nat, exp as nat)
    decreases exp
{
    if exp == 0 {
        1
    } else {
        base * exec_pow(base, exp - 1)
    }
}

fn exec_sum_powers(n: u32, k: u32) -> (result: u32)
    ensures result as nat == sum_powers(n as nat, k as nat)
    decreases n
{
    if n == 0 {
        0
    } else {
        exec_pow(n % 10, k) + exec_sum_powers(n / 10, k)
    }
}
// </vc-helpers>

// <vc-spec>
fn is_armstrong(n: u32) -> (result: bool)
    ensures 
        result == (n as nat == sum_powers(n as nat, count_digits(n as nat))),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Removed casting n to nat in executable code, now directly compare u32 values */
{
    let k = exec_count_digits(n);
    let sum = exec_sum_powers(n, k);
    sum == n
}
// </vc-code>

}
fn main() {}