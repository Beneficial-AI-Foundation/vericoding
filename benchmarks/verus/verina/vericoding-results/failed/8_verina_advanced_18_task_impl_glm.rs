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
fn count_digits_exec(n: nat) -> (result: nat)
    decreases n
    ensures result == count_digits(n)
{
    if n == 0 {
        1
    } else if n < 10 {
        1
    } else {
        1 + count_digits_exec(n / 10)
    }
}

fn pow_nat_exec(base: nat, exp: nat) -> (result: nat)
    decreases exp
    ensures result == pow_nat(base, exp)
{
    if exp == 0 {
        1
    } else {
        base * pow_nat_exec(base, (exp - 1) as nat)
    }
}

fn sum_powers_exec(n: nat, k: nat) -> (result: nat)
    decreases n
    ensures result == sum_powers(n, k)
{
    if n == 0 {
        0
    } else {
        pow_nat_exec(n % 10, k) + sum_powers_exec(n / 10, k)
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
    let n_nat = n as nat;
    let k = count_digits_exec(n_nat);
    let s = sum_powers_exec(n_nat, k);
    n_nat == s
}
// </vc-code>

}
fn main() {}