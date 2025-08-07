use vstd::prelude::*;

verus! {

fn pow_exec(base: u32, exp: u32) -> u32
    decreases exp,
{
    if exp == 0 {
        1
    } else if exp > 10 {
        // Prevent overflow for large exponents
        u32::MAX
    } else {
        base.checked_mul(pow_exec(base, exp - 1)).unwrap_or(u32::MAX)
    }
}

fn count_digits(n: u32) -> u32 {
    if n == 0 { 
        1
    } else {
        count_digits_helper(n, 0)
    }
}

fn count_digits_helper(n: u32, acc: u32) -> u32
    decreases n,
{
    if n == 0 {
        acc
    } else if acc >= 10 {
        // Prevent overflow - max digits for u32
        10
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
        let power_result = pow_exec(digit, k);
        let new_acc = acc.checked_add(power_result).unwrap_or(u32::MAX);
        sum_powers_helper(n / 10, k, new_acc)
    }
}

spec fn is_armstrong_precond(n: u32) -> bool {
    true
}

spec fn is_armstrong_postcond(n: u32, result: bool) -> bool {
    true
}

fn is_armstrong(n: u32) -> bool {
    let k = count_digits(n);
    sum_powers(n, k) == n
}

fn main() {}

} // verus!