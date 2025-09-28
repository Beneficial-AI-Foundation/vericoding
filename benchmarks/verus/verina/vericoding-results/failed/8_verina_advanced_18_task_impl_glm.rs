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
/* helper modified by LLM (iteration 2): added decreases clause to loop */
fn count_digits_exec(n: u32) -> (k: u32)
    ensures k == count_digits(n as nat)
{
    if n == 0 {
        1
    } else {
        let mut count = 0;
        let mut temp = n;
        while temp != 0
            invariant
                temp <= n,
                count <= 10,
                count + count_digits(temp as nat) == count_digits(n as nat),
            decreases temp
        {
            count += 1;
            temp /= 10;
        }
        count
    }
}

/* helper modified by LLM (iteration 2): added decreases clause to loop */
fn pow_exec(base: u32, exp: u32) -> (result: u32)
    ensures result == pow_nat(base as nat, exp as nat)
{
    if exp == 0 {
        1
    } else {
        let mut result = 1;
        let mut i = 0;
        while i < exp
            invariant
                i <= exp,
                result == pow_nat(base as nat, i as nat),
            decreases exp - i
        {
            result *= base;
            i += 1;
        }
        result
    }
}

/* helper modified by LLM (iteration 2): added decreases clause to loop */
fn sum_powers_exec(n: u32, k: u32) -> (sum: u64)
    ensures sum == sum_powers(n as nat, k as nat)
{
    if n == 0 {
        0
    } else {
        let mut sum = 0;
        let mut temp = n;
        while temp != 0
            invariant
                temp <= n,
                sum + sum_powers(temp as nat, k as nat) == sum_powers(n as nat, k as nat),
            decreases temp
        {
            let digit = temp % 10;
            sum += pow_exec(digit, k) as u64;
            temp /= 10;
        }
        sum
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
    if n == 0 {
        true
    } else {
        let k = count_digits_exec(n);
        let sum = sum_powers_exec(n, k);
        sum == n as u64
    }
}
// </vc-code>

}
fn main() {}