use vstd::prelude::*;

verus! {

fn pow_exec(base: u32, exp: u32) -> u32
    decreases exp,
{
    if exp == 0 {
        1
    } else {
        base * pow_exec(base, exp - 1)
    }
}

fn count_digits(n: u32) -> u32 {
    count_digits_helper(n, 0)
}

fn count_digits_helper(n: u32, acc: u32) -> u32
    decreases n,
{
    if n == 0 {
        if acc == 0 { 1 } else { acc }
    } else {
        count_digits_helper(n / 10, acc + 1)
    }
}

fn sum_powers(n: u32, k: u32) -> u32 {
    sum_powers_helper(n, k, 0)
}

fn sum_powers_helper(n: u32, k: u32, acc: u32) -> u32
    decreases n,
{
    if n == 0 {
        acc
    } else {
        let digit = n % 10;
        let power = pow_exec(digit, k);
        sum_powers_helper(n / 10, k, acc + power)
    }
}

spec fn is_armstrong_precond(n: u32) -> bool {
    true
}

spec fn is_armstrong_postcond(n: u32, result: bool) -> bool {
    true
}

fn is_armstrong(n: u32) -> bool {
    let num_digits = count_digits(n);
    let sum = sum_powers(n, num_digits);
    n == sum
}

fn main() {}

} // verus!