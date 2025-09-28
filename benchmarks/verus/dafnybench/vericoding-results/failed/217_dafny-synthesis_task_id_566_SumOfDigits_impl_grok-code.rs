use vstd::prelude::*;

verus! {

// spec fn int_values(n: int) -> Seq<int>
//     recommends n >= 0
// {
//     if n == 0 { seq![0] }
//     else { seq![n] + int_values(n/10) }
// }

spec fn power10(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 10 * power10((n - 1) as nat) }
}

// spec fn number_to_seq(number: int) -> Seq<int>
//     recommends number >= 0
// {
//     if number == 0 { Seq::empty() }
//     else { seq![number % 10] + number_to_seq(number/10) }
// }

// spec fn sum_seq(digits: Seq<int>) -> int
// {
//     if digits.len() == 0 { 0 }
//     else { digits[0] + sum_seq(digits.subrange(1, digits.len() as int)) }
// }

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

// <vc-helpers>
spec fn sum_of_digits_spec(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 } else { (n % 10) + sum_of_digits_spec((n / 10) as nat) }
}

proof fn lemma_sum_digits_spec_equals(number: nat)
    ensures sum_of_digits_spec(number) == sum_digits(number)
    decreases number
{
    if number <= 9 {
    } else {
        lemma_sum_digits_spec_equals((number / 10) as nat);
    }
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
    proof {
        lemma_sum_digits_spec_equals(number as nat);
    }
    let mut n: u64 = number;
    let mut s: u64 = 0;
    while n > 0
        decreases n
        invariant {
            0 <= n,
            s as nat + sum_of_digits_spec(n as nat) == sum_of_digits_spec(number as nat)
        }
    {
        let digit = n % 10;
        s = s + digit;
        n = n / 10;
    }
    s
}
// </vc-code>

fn main() {}

}