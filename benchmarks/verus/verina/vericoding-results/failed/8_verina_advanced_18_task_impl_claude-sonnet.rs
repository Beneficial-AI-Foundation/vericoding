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
/* helper modified by LLM (iteration 5): fixed ghost cast in lemma proof */

fn lemma_count_digits_positive(n: nat)
    ensures count_digits(n) > 0
    decreases n
{
    if n == 0 {
        assert(count_digits(0) == 1);
    } else if n < 10 {
        assert(count_digits(n) == 1);
    } else {
        lemma_count_digits_positive(n / 10);
        assert(count_digits(n) == 1 + count_digits(n / 10));
    }
}

fn lemma_pow_nat_positive(base: nat, exp: nat)
    ensures pow_nat(base, exp) > 0
    decreases exp
{
    if exp == 0 {
        assert(pow_nat(base, 0) == 1);
    } else {
        lemma_pow_nat_positive(base, exp - 1);
        assert(pow_nat(base, exp) == base * pow_nat(base, exp - 1));
    }
}

fn count_digits_exec(n: u32) -> (result: u32)
    requires n > 0
    ensures result == count_digits(n as nat),
            result <= 10
    decreases n
{
    if n < 10 {
        1
    } else {
        let rest = count_digits_exec(n / 10);
        rest + 1
    }
}

fn pow_nat_exec(base: u32, exp: u32) -> (result: u32)
    requires base <= 9,
             exp <= 10
    ensures result == pow_nat(base as nat, exp as nat)
    decreases exp
{
    if exp == 0 {
        1
    } else {
        let rest = pow_nat_exec(base, exp - 1);
        base * rest
    }
}

fn sum_powers_exec(n: u32, k: u32) -> (result: u32)
    requires k <= 10
    ensures result == sum_powers(n as nat, k as nat)
    decreases n
{
    if n == 0 {
        0
    } else {
        let digit = n % 10;
        let power = pow_nat_exec(digit, k);
        let rest = sum_powers_exec(n / 10, k);
        power + rest
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
    /* code modified by LLM (iteration 5): handling special case of 0 and adding overflow safety */
    if n == 0 {
        let sum = sum_powers_exec(0, 1);
        return n == sum;
    }
    
    let digit_count = count_digits_exec(n);
    let sum = sum_powers_exec(n, digit_count);
    n == sum
}
// </vc-code>

}
fn main() {}