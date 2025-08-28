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
proof fn sum_digits_recursive_correct(n: nat, p: nat)
    requires p > 0
    ensures sum_digits_recursive(n, p) == sum_digits_recursive_impl(n, p)
    decreases p
{
    if n == 0 || p == 0 {
        assert(sum_digits_recursive(n, p) == 0);
        assert(sum_digits_recursive_impl(n, p) == 0);
    } else {
        let left_most_digit = n/p;
        let rest = n%p;
        if p < 10 {
            assert(sum_digits_recursive(n, p) == left_most_digit + sum_digits_recursive(rest, (p/10) as nat));
            assert((p/10) as nat == 0);
            assert(sum_digits_recursive(rest, 0) == 0);
            assert(sum_digits_recursive(n, p) == left_most_digit);
            assert(sum_digits_recursive_impl(n, p) == left_most_digit);
        } else {
            sum_digits_recursive_correct(rest, (p/10) as nat);
            assert(sum_digits_recursive(rest, (p/10) as nat) == sum_digits_recursive_impl(rest, (p/10) as nat));
            assert(sum_digits_recursive(n, p) == left_most_digit + sum_digits_recursive(rest, (p/10) as nat));
            assert(sum_digits_recursive_impl(n, p) == left_most_digit + sum_digits_recursive_impl(rest, (p/10) as nat));
        }
    }
}

spec fn sum_digits_recursive_impl(n: nat, p: nat) -> nat
    decreases p
{
    if n == 0 || p == 0 { 0 }
    else {
        let left_most_digit = n/p;
        let rest = n%p;
        if p < 10 { left_most_digit }
        else { left_most_digit + sum_digits_recursive_impl(rest, (p/10) as nat) }
    }
}

proof fn power10_positive(n: nat)
    ensures power10(n) > 0
    decreases n
{
    if n == 0 {
    } else {
        power10_positive((n - 1) as nat);
    }
}

proof fn number_of_digits_positive(n: nat)
    ensures number_of_digits(n) > 0
    decreases n
{
    if 0 <= n <= 9 {
    } else {
        number_of_digits_positive((n/10) as nat);
    }
}

proof fn sum_digits_simple_correct(n: nat)
    ensures sum_digits_simple(n) == sum_digits(n)
    decreases n
{
    reveal(sum_digits_simple);
    reveal(sum_digits);
}

spec fn sum_digits_simple(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 }
    else { (n % 10) + sum_digits_simple((n/10) as nat) }
}

proof fn sum_digits_bound(n: nat)
    ensures sum_digits_simple(n) <= n * 9
    decreases n
{
    if n == 0 {
        assert(sum_digits_simple(0) == 0);
        assert(0 <= 0 * 9);
    } else {
        sum_digits_bound((n/10) as nat);
        assert(n % 10 <= 9);
        assert(sum_digits_simple((n/10) as nat) <= (n/10) as nat * 9);
        assert(sum_digits_simple(n) == (n % 10) + sum_digits_simple((n/10) as nat));
        assert(sum_digits_simple(n) <= 9 + (n/10) as nat * 9);
        assert(9 + (n/10) as nat * 9 <= n * 9);
    }
}

proof fn sum_digits_simple_property(n: nat)
    ensures n > 0 ==> sum_digits_simple(n) == (n % 10) + sum_digits_simple((n/10) as nat)
    decreases n
{
    if n > 0 {
        assert(sum_digits_simple(n) == (n % 10) + sum_digits_simple((n/10) as nat));
    }
}

proof fn sum_overflow_bound(number: u64)
    ensures sum_digits_simple(number as nat) <= u64::MAX
{
    sum_digits_bound(number as nat);
    assert(sum_digits_simple(number as nat) <= (number as nat) * 9);
    assert((number as nat) * 9 <= u64::MAX as nat * 9);
    assert(u64::MAX as nat * 9 <= u64::MAX as nat);
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn sum_of_digits(number: u64) -> (sum: u64)
    requires number >= 0,
    ensures 
        sum >= 0,
        sum == sum_digits(number as nat),
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if number == 0 {
        return 0;
    }
    
    let mut n = number;
    let mut sum: u64 = 0;
    
    proof {
        sum_digits_simple_correct(number as nat);
        sum_digits_bound(number as nat);
        sum_overflow_bound(number);
    }
    
    while n > 0
        invariant 
            n <= number,
            sum <= number * 9,
            sum + sum_digits_simple(n as nat) == sum_digits_simple(number as nat),
            sum <= u64::MAX - 9
        decreases n
    {
        let digit = n % 10;
        proof {
            sum_digits_simple_property(n as nat);
            assert(sum_digits_simple(n as nat) == digit + sum_digits_simple((n/10) as nat));
        }
        n = n / 10;
        proof {
            assert(digit <= 9);
            assert(sum <= u64::MAX - 9);
            assert(sum + digit <= u64::MAX);
        }
        sum = sum + digit;
        proof {
            assert(sum_digits_simple((n/10) as nat) == sum_digits_simple(n as nat));
            assert(sum == (sum - digit) + digit);
            assert((sum - digit) + (digit + sum_digits_simple(n as nat)) == sum_digits_simple(number as nat));
            assert(sum + sum_digits_simple(n as nat) == sum_digits_simple(number as nat));
        }
    }
    
    proof {
        assert(n == 0);
        assert(sum_digits_simple(0) == 0);
        assert(sum + 0 == sum_digits_simple(number as nat));
        assert(sum == sum_digits_simple(number as nat));
        assert(sum_digits_simple(number as nat) == sum_digits(number as nat));
    }
    
    sum
}
// </vc-code>

fn main() {}

}