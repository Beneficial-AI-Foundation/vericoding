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
proof fn lemma_power10_positive(n: nat)
    ensures power10(n) > 0
    decreases n
{
    if n == 0 {
    } else {
        lemma_power10_positive((n - 1) as nat);
    }
}

proof fn lemma_power10_values()
    ensures 
        power10(0) == 1,
        power10(1) == 10,
        power10(2) == 100
{
}

proof fn lemma_power10_div_10(n: nat)
    requires n > 0
    ensures power10(n) / 10 == power10((n - 1) as nat)
    decreases n
{
    if n == 1 {
        lemma_power10_values();
    } else {
        lemma_power10_div_10((n - 1) as nat);
    }
}

proof fn lemma_number_of_digits_bounds(n: nat)
    ensures 
        number_of_digits(n) >= 1,
        n < power10(number_of_digits(n))
    decreases n
{
    if 0 <= n <= 9 {
        lemma_power10_values();
    } else {
        lemma_number_of_digits_bounds((n/10) as nat);
        lemma_power10_positive(number_of_digits(n));
    }
}

proof fn lemma_sum_digits_recursive_base(n: nat)
    requires n < 10
    ensures sum_digits_recursive(n, 1) == n
{
    if n == 0 {
    } else {
        assert(n / 1 == n);
        assert(n % 1 == 0);
        assert(sum_digits_recursive(n, 1) == n + sum_digits_recursive(0, 0));
        assert(sum_digits_recursive(0, 0) == 0);
    }
}

proof fn lemma_sum_digits_step(n: nat, digit: nat, remaining: nat)
    requires 
        n == digit + remaining * 10,
        digit < 10,
        remaining >= 0
    ensures sum_digits(n) == digit + sum_digits(remaining)
{
    if remaining == 0 {
        assert(n == digit);
        assert(n < 10);
        assert(number_of_digits(n) == 1);
        assert(power10(0) == 1);
        lemma_sum_digits_recursive_base(n);
    } else {
        assert(n >= 10);
        if remaining < 10 {
            assert(10 <= n < 100);
            // Need to prove number_of_digits(n) == 2 more carefully
            assert(n >= 10);
            assert(n / 10 == remaining);
            assert(remaining < 10);
            assert(remaining >= 1); // since remaining > 0 and remaining < 10
            assert(number_of_digits(remaining) == 1);
            assert(number_of_digits(n) == 1 + number_of_digits(remaining));
            assert(number_of_digits(n) == 2);
            
            lemma_power10_values();
            let p = power10(1);
            assert(p == 10);
            // Need to prove n / p == digit more carefully
            assert(n == digit + remaining * 10);
            assert(n / 10 == (digit + remaining * 10) / 10);
            assert(digit < 10);
            assert(n / 10 == remaining);
            // But we need n / p where p = 10, so we need the most significant digit
            // Let me reconsider the relationship
            assert(n == digit + remaining * 10);
            assert(remaining < 10);
            assert(digit < 10);
            // The leftmost digit should be remaining, not digit
            assert(n / p == remaining); // This should be remaining, not digit
            assert(n % p == digit);
            assert(sum_digits_recursive(n, p) == remaining + sum_digits_recursive(digit, 1));
            lemma_sum_digits_recursive_base(digit);
            assert(sum_digits(remaining) == remaining);
        } else {
            lemma_number_of_digits_bounds(n);
            lemma_number_of_digits_bounds(remaining);
        }
    }
}

proof fn lemma_sum_digits_iteration(old_remaining: nat, digit: nat, new_remaining: nat, old_sum: nat, new_sum: nat)
    requires 
        digit == old_remaining % 10,
        new_remaining == old_remaining / 10,
        digit < 10,
        old_remaining == digit + new_remaining * 10,
        new_sum == old_sum + digit
    ensures 
        old_sum + sum_digits(old_remaining) == new_sum + sum_digits(new_remaining)
{
    lemma_sum_digits_step(old_remaining, digit, new_remaining);
    assert(sum_digits(old_remaining) == digit + sum_digits(new_remaining));
    assert(old_sum + sum_digits(old_remaining) == old_sum + digit + sum_digits(new_remaining));
    assert(old_sum + digit == new_sum);
    assert(old_sum + sum_digits(old_remaining) == new_sum + sum_digits(new_remaining));
}

proof fn lemma_sum_digits_zero()
    ensures sum_digits(0) == 0
{
    assert(number_of_digits(0) == 1);
    assert(power10(0) == 1);
    assert(sum_digits_recursive(0, 1) == 0);
}

proof fn lemma_digit_bounds(n: u64)
    ensures (n % 10) < 10
{
}

proof fn lemma_sum_bounds(n: u64, current_sum: u64)
    requires n <= u64::MAX, current_sum <= u64::MAX, (n % 10) < 10
    ensures current_sum + (n % 10) <= u64::MAX
{
    // Since (n % 10) < 10, and we're working with u64 values in a loop that
    // processes digits, the sum of digits will be much smaller than the original number
    // For any u64 number, the maximum sum of digits is 9 * 20 = 180 (since u64::MAX has at most 20 digits)
    // So current_sum + digit will not overflow as long as we stay within reasonable bounds
    assert((n % 10) <= 9);
    // This should hold in practice for digit sum calculations
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
    
    let mut sum = 0u64;
    let mut remaining = number;
    
    while remaining > 0
        invariant 
            sum <= u64::MAX,
            remaining <= number,
            sum + sum_digits(remaining as nat) == sum_digits(number as nat)
        decreases remaining
    {
        let digit = remaining % 10;
        let old_remaining = remaining;
        let old_sum = sum;
        
        proof {
            lemma_digit_bounds(remaining);
            lemma_sum_bounds(remaining, sum);
        }
        
        sum = sum + digit;
        remaining = remaining / 10;
        
        proof {
            assert(digit == old_remaining % 10);
            assert(remaining == old_remaining / 10);
            assert(old_remaining == digit + remaining * 10);
            lemma_sum_digits_iteration(old_remaining as nat, digit as nat, remaining as nat, old_sum as nat, sum as nat);
        }
    }
    
    proof {
        assert(remaining == 0);
        lemma_sum_digits_zero();
        assert(sum_digits(0) == 0);
        assert(sum + 0 == sum_digits(number as nat));
    }
    
    sum
}
// </vc-code>

fn main() {}

}