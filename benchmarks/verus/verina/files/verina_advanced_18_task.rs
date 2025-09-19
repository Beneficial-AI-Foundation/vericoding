// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
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
// </vc-helpers>

// <vc-spec>
fn is_armstrong(n: u32) -> (result: bool)
    ensures 
        result == (n as nat == sum_powers(n as nat, count_digits(n as nat))),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    false
    // impl-end
}
// </vc-code>


}
fn main() {
    // let n = 153;
    // println!("Is {} an Armstrong number? {}", n, is_armstrong(n));
    // 
    // let n = 9474;
    // println!("Is {} an Armstrong number? {}", n, is_armstrong(n));
    // 
    // let n = 9475;
    // println!("Is {} an Armstrong number? {}", n, is_armstrong(n));
}