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
proof fn lemma_div_mod(n: nat, d: nat)
    requires
        d > 0,
    ensures
        n == d * (n / d) + n % d,
        n % d < d,
        n / d <= n,
{
    // Built-in Verus knowledge about division and modulus
}

proof fn lemma_sum_digits_recursive_works(n: nat, p: nat)
    requires
        p > 0,
        p == power10((number_of_digits(n) - 1) as nat),
    ensures
        sum_digits_recursive(n, p) == sum_digits(n),
    decreases p
{
    reveal(sum_digits);
    reveal(sum_digits_recursive);
    
    if n == 0 {
        assert(sum_digits_recursive(n, p) == 0);
        assert(sum_digits(n) == 0);
    } else if p == 0 {
    } else {
        let left_most_digit = n / p;
        let rest = n % p;
        lemma_div_mod(n, p);
        assert(rest < p);
        
        if rest > 0 {
            lemma_number_of_digits_positive(rest);
            let new_p = power10((number_of_digits(rest) - 1) as nat);
            lemma_power10_positive((number_of_digits(rest) - 1) as nat);
            lemma_sum_digits_recursive_works(rest, new_p);
        } else {
            assert(sum_digits_recursive(rest, (p/10) as nat) == 0);
        }
        
        assert(sum_digits_recursive(n, p) == left_most_digit + sum_digits_recursive(rest, (p/10) as nat));
    }
}

proof fn lemma_sum_digits_recursive_step(n: nat, p: nat)
    requires
        n > 0,
        p > 0,
        p == power10((number_of_digits(n) - 1) as nat),
    ensures
        sum_digits(n) == (n / p) as nat + sum_digits((n % p) as nat),
{
    lemma_sum_digits_recursive_works(n, p);
    reveal(sum_digits_recursive);
    
    let left_most_digit = n / p;
    let rest = n % p;
    lemma_div_mod(n, p);
    assert(rest < p);
    
    if rest > 0 {
        lemma_number_of_digits_positive(rest);
        let new_p = power10((number_of_digits(rest) - 1) as nat);
        lemma_power10_positive((number_of_digits(rest) - 1) as nat);
        lemma_sum_digits_recursive_works(rest, new_p);
    }
    
    assert(sum_digits_recursive(n, p) == left_most_digit + sum_digits_recursive(rest, (p/10) as nat));
    assert(sum_digits(n) == left_most_digit + sum_digits(rest));
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
    let mut n = number;
    let mut sum: u64 = 0;
    
    proof {
        lemma_sum_digits_nonnegative(n as nat);
    }
    
    while n > 0
        invariant
            n >= 0,
            sum >= 0,
            sum as nat + sum_digits(n as nat) == sum_digits(number as nat),
        decreases n
    {
        let old_n = n;
        let digit = n % 10;
        assert(digit <= 9);
        assert(sum + digit >= sum);
        sum = sum + digit;
        n = n / 10;
        
        proof {
            let ndigits = number_of_digits(old_n as nat);
            lemma_number_of_digits_positive(old_n as nat);
            let p = power10((ndigits - 1) as nat);
            lemma_power10_positive((ndigits - 1) as nat);
            
            lemma_sum_digits_recursive_step(old_n as nat, p);
            assert(sum_digits(old_n as nat) == digit as nat + sum_digits(n as nat));
            
            assert((sum - digit) as nat + sum_digits(old_n as nat) == (sum - digit) as nat + digit as nat + sum_digits(n as nat));
            assert(sum as nat + sum_digits(n as nat) == (sum - digit) as nat + digit as nat + sum_digits(n as nat));
        }
    }
    
    sum
}
// </vc-code>

fn main() {}

}