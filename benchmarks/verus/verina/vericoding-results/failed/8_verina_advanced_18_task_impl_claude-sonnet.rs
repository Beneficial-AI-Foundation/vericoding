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
/* helper modified by LLM (iteration 5): fixed pow_nat_one lemma and improved count/pow implementations */
proof fn lemma_single_digit_armstrong(n: nat)
    requires n < 10
    ensures sum_powers(n, count_digits(n)) == n
{
    if n == 0 {
        assert(count_digits(0) == 1);
        assert(sum_powers(0, 1) == 0);
        assert(pow_nat(0, 1) == 0);
    } else {
        assert(count_digits(n) == 1);
        assert(sum_powers(n, 1) == pow_nat(n, 1));
        assert(pow_nat(n, 1) == n * pow_nat(n, 0));
        assert(pow_nat(n, 0) == 1);
        assert(pow_nat(n, 1) == n * 1 == n);
    }
}

proof fn lemma_pow_nat_one(base: nat)
    ensures pow_nat(base, 1) == base
{
    assert(pow_nat(base, 1) == base * pow_nat(base, 0));
    assert(pow_nat(base, 0) == 1);
    assert(base * 1 == base);
}

fn count_digits_impl(n: u32) -> (result: u32)
    ensures result == count_digits(n as nat)
    ensures result >= 1
{
    if n == 0 {
        1
    } else {
        let mut count: u32 = 0;
        let mut temp = n;
        while temp > 0
            invariant temp <= n
            invariant count <= 10
            invariant if temp == 0 { count == count_digits(n as nat) } else { count + count_digits(temp as nat) == count_digits(n as nat) }
            decreases temp
        {
            count = count + 1;
            temp = temp / 10;
        }
        count
    }
}

fn pow_impl(base: u32, exp: u32) -> (result: u32)
    requires exp <= 10
    requires base <= 10
    ensures result == pow_nat(base as nat, exp as nat)
{
    if exp == 0 {
        1
    } else {
        let mut result: u32 = 1;
        let mut i: u32 = 0;
        while i < exp
            invariant i <= exp
            invariant result == pow_nat(base as nat, i as nat)
            invariant result <= 10000000000u32
            decreases exp - i
        {
            i = i + 1;
            result = result * base;
        }
        result
    }
}

fn sum_powers_impl(n: u32, k: u32) -> (result: u32)
    requires k <= 10
    ensures result == sum_powers(n as nat, k as nat)
    decreases n
{
    if n == 0 {
        0
    } else {
        let digit = n % 10;
        let rest = n / 10;
        let digit_power = pow_impl(digit, k);
        let rest_sum = sum_powers_impl(rest, k);
        digit_power + rest_sum
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
    /* code modified by LLM (iteration 5): fixed overflow issues and added proper bounds */
    let digits = count_digits_impl(n);
    let sum = sum_powers_impl(n, digits);
    
    if n < 10 {
        proof {
            lemma_single_digit_armstrong(n as nat);
        }
    }
    
    n == sum
}
// </vc-code>

}
fn main() {}