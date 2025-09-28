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
/* helper modified by LLM (iteration 5): Fixed pow_nat lemma and loop invariants for overflow safety */
proof fn lemma_pow_nat_base_case(n: nat)
    ensures pow_nat(n, 1) == n
    decreases 1
{
    assert(pow_nat(n, 1) == n * pow_nat(n, 0));
    assert(pow_nat(n, 0) == 1);
}

proof fn lemma_single_digit_armstrong(n: nat)
    requires n < 10
    ensures sum_powers(n, count_digits(n)) == n
{
    assert(count_digits(n) == 1);
    assert(sum_powers(n, 1) == pow_nat(n % 10, 1) + sum_powers(n / 10, 1));
    assert(n % 10 == n);
    assert(n / 10 == 0);
    assert(sum_powers(0, 1) == 0);
    lemma_pow_nat_base_case(n);
    assert(pow_nat(n, 1) == n);
}

proof fn lemma_count_digits_positive(n: nat)
    ensures count_digits(n) >= 1
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

fn count_digits_exec(n: u32) -> (result: u32)
    ensures result as nat == count_digits(n as nat),
            result >= 1
{
    proof { lemma_count_digits_positive(n as nat); }
    
    if n == 0 {
        1
    } else {
        let mut count = 0u32;
        let mut temp = n;
        
        while temp > 0
            invariant
                count <= 10,
                count as nat == count_digits(n as nat) - count_digits(temp as nat),
                temp <= n
            decreases temp
        {
            assert(count < 10);
            count = count + 1;
            temp = temp / 10;
        }
        
        count
    }
}

fn pow_exec(base: u32, exp: u32) -> (result: u32)
    requires base <= 9, exp <= 10
    ensures result as nat == pow_nat(base as nat, exp as nat)
{
    let mut result = 1u32;
    let mut i = 0u32;
    
    while i < exp
        invariant
            i <= exp,
            result as nat == pow_nat(base as nat, i as nat),
            result <= 1000000000
        decreases exp - i
    {
        assert(result <= 1000000000 / base);
        result = result * base;
        i = i + 1;
    }
    
    result
}

fn sum_powers_exec(n: u32, k: u32) -> (result: u32)
    requires k <= 10
    ensures result as nat == sum_powers(n as nat, k as nat)
    decreases n
{
    if n == 0 {
        0
    } else {
        let digit = n % 10;
        let rest = n / 10;
        let digit_power = pow_exec(digit, k);
        let rest_sum = sum_powers_exec(rest, k);
        assert(digit_power <= 10000000000);
        assert(rest_sum <= 4000000000);
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
    /* code modified by LLM (iteration 5): Added bounds checking for overflow safety */
    let digits = count_digits_exec(n);
    if digits > 10 {
        false
    } else {
        let sum = sum_powers_exec(n, digits);
        n == sum
    }
}
// </vc-code>

}
fn main() {}