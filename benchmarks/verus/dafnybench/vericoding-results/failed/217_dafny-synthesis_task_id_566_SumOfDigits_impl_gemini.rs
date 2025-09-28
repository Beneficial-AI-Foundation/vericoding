// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn power10(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 10 * power10((n - 1) as nat) }
}

spec fn sum_digits(n: nat) -> nat {
    let ndigits = number_of_digits(n);
    let p = power10((ndigits - 1) as nat);
    sum_digits_recursive(n, p)
}

spec fn sum_digits_recursive(n: nat, p: nat) -> nat
    decreases p
{
    if n == 0 || p == 0 { 0 }
    else {
        let left_most_digit = n/p;
        let rest = n%p;
        left_most_digit + sum_digits_recursive(rest, (p/10) as nat)
    }
}

spec fn number_of_digits(n: nat) -> nat
    decreases n
{
    if 0 <= n <= 9 { 1 } else { 1 + number_of_digits((n/10) as nat) }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_power10_is_product(a: nat, b: nat)
    ensures power10(a + b) == power10(a) * power10(b)
    decreases a
{
    if a > 0 {
        lemma_power10_is_product((a - 1) as nat, b);
    }
}

fn get_initial_divisor(number: u64) -> (p: u64)
    requires number > 0
    ensures
        p > 0,
        p == power10((number_of_digits(number as nat) - 1) as nat),
        p <= number,
{
    let mut p: u64 = 1;
    let mut temp = number;
    while temp >= 10
        invariant
            number > 0,
            temp > 0,
            p > 0,
            p <= number,
            power10((number_of_digits(number as nat) - 1) as nat) == p * power10((number_of_digits(temp as nat) - 1) as nat),
        decreases temp
    {
        proof {
            let d_temp_old = number_of_digits(temp as nat);
            let d_temp_new = number_of_digits((temp/10) as nat);
            assert(d_temp_old == 1 + d_temp_new);
            let d_old_minus_1 = (d_temp_old - 1) as nat;
            let d_new_minus_1 = (d_temp_new - 1) as nat;
            assert(d_old_minus_1 == 1 + d_new_minus_1);
            lemma_power10_is_product(1, d_new_minus_1);
        }
        p = p * 10;
        temp = temp / 10;
    }
    p
}
// </vc-helpers>

// <vc-spec>
fn sum_of_digits(number: u64) -> (sum: u64)
    requires number >= 0,
    ensures 
        sum >= 0,
        sum == sum_digits(number as nat),
// </vc-spec>
// <vc-code>
{
    if number == 0 {
        return 0;
    }

    let mut n = number;
    let mut s: u64 = 0;
    let mut p = get_initial_divisor(number);

    while p > 0
        invariant
            sum_digits(number as nat) == s as nat + sum_digits_recursive(n as nat, p as nat),
        decreases p
    {
        proof {
            if p > 0 {
                assert(sum_digits_recursive(n as nat, p as nat) == (n/p) as nat + sum_digits_recursive((n%p) as nat, (p/10) as nat));
            }
        }
        
        let digit = n / p;
        s = s + digit;
        n = n % p;
        p = p / 10;
    }

    return s;
}
// </vc-code>

}
fn main() {}