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
        assert(power10(0) == 1);
    } else {
        lemma_power10_positive((n - 1) as nat);
        assert(power10(n) == 10 * power10((n - 1) as nat));
    }
}

proof fn lemma_power10_monotonic(n: nat, m: nat)
    requires n <= m
    ensures power10(n) <= power10(m)
    decreases m - n
{
    if n == m {
        assert(power10(n) == power10(m));
    } else {
        lemma_power10_monotonic(n, (m - 1) as nat);
        lemma_power10_positive((m - 1) as nat);
        assert(power10(m) == 10 * power10((m - 1) as nat));
        assert(power10(n) <= power10((m - 1) as nat));
        assert(power10(n) <= power10(m));
    }
}

proof fn lemma_number_of_digits_bounds(n: nat)
    ensures 
        number_of_digits(n) >= 1,
        n < power10(number_of_digits(n)),
        n >= power10((number_of_digits(n) - 1) as nat)
    decreases n
{
    if 0 <= n && n <= 9 {
        assert(number_of_digits(n) == 1);
        assert(power10(1) == 10);
        assert(power10(0) == 1);
        assert(n < 10);
        if n == 0 {
            assert(n >= 0);
        } else {
            assert(n >= 1);
        }
        assert(n >= power10(0));
    } else {
        assert(n >= 10);
        assert(n >= 1);
        assert(n >= power10(0));
        lemma_number_of_digits_bounds((n/10) as nat);
        assert(number_of_digits(n) == 1 + number_of_digits((n/10) as nat));
        let d = number_of_digits((n/10) as nat);
        assert(n/10 < power10(d));
        assert(n < 10 * power10(d));
        assert(power10(d + 1) == 10 * power10(d));
        assert(n < power10(number_of_digits(n)));
        
        // For the lower bound
        assert(n/10 >= power10((d - 1) as nat));
        assert(n >= 10 * power10((d - 1) as nat));
        assert(power10(d) == 10 * power10((d - 1) as nat));
        assert(n >= power10(d));
        assert(number_of_digits(n) == d + 1);
        assert(n >= power10((number_of_digits(n) - 1) as nat));
    }
}

proof fn lemma_sum_digits_recursive_step(n: nat, p: nat)
    requires p > 0
    ensures sum_digits_recursive(n, p) == n/p + sum_digits_recursive(n%p, (p/10) as nat)
    decreases p
{
    if n == 0 {
        assert(sum_digits_recursive(n, p) == 0);
        assert(n/p == 0);
        assert(n%p == 0);
        assert(sum_digits_recursive(0, (p/10) as nat) == 0);
    } else {
        assert(sum_digits_recursive(n, p) == n/p + sum_digits_recursive(n%p, (p/10) as nat));
    }
}

proof fn lemma_number_of_digits_div10(n: nat)
    requires n >= 10
    ensures number_of_digits(n) == 1 + number_of_digits((n/10) as nat)
{
    assert(n > 9);
}

proof fn lemma_digit_bound(n: nat, p: nat)
    requires p > 0, n < 10 * p
    ensures n / p <= 9
{
    assert(n < 10 * p);
    assert(n / p < 10);
    assert(n / p <= 9);
}

proof fn lemma_sum_digits_bound(n: nat)
    ensures sum_digits(n) <= n
    decreases n
{
    let ndigits = number_of_digits(n);
    let p = power10((ndigits - 1) as nat);
    lemma_sum_digits_recursive_bound(n, p);
    assert(sum_digits(n) == sum_digits_recursive(n, p));
}

proof fn lemma_sum_digits_recursive_bound(n: nat, p: nat)
    ensures sum_digits_recursive(n, p) <= n
    decreases p
{
    if n == 0 || p == 0 {
        assert(sum_digits_recursive(n, p) == 0);
        assert(0 <= n);
    } else {
        let left_most_digit = n/p;
        let rest = n%p;
        lemma_sum_digits_recursive_bound(rest, (p/10) as nat);
        assert(sum_digits_recursive(rest, (p/10) as nat) <= rest);
        assert(n == left_most_digit * p + rest);
        assert(left_most_digit <= n/p);
        assert(sum_digits_recursive(n, p) == left_most_digit + sum_digits_recursive(rest, (p/10) as nat));
        assert(sum_digits_recursive(n, p) <= left_most_digit + rest);
        assert(left_most_digit + rest <= left_most_digit * p + rest);
        assert(left_most_digit * p + rest == n);
        assert(sum_digits_recursive(n, p) <= n);
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
    let mut sum: u64 = 0;
    let mut remaining = number;
    
    let ndigits = if number == 0 {
        1u64
    } else {
        let mut count: u64 = 0;
        let mut temp = number;
        
        while temp > 0
            invariant
                0 <= temp <= number,
                temp == 0 ==> count == number_of_digits(number as nat),
                temp > 0 ==> count + number_of_digits(temp as nat) == number_of_digits(number as nat),
                count <= number_of_digits(number as nat),
                count <= u64::MAX - 1,
            decreases temp
        {
            proof {
                if temp >= 10 {
                    lemma_number_of_digits_div10(temp as nat);
                    assert(number_of_digits(temp as nat) == 1 + number_of_digits((temp/10) as nat));
                    assert(count + 1 + number_of_digits((temp/10) as nat) == number_of_digits(number as nat));
                } else {
                    assert(0 < temp <= 9);
                    assert(number_of_digits(temp as nat) == 1);
                    assert(count + 1 == number_of_digits(number as nat));
                }
                assert(count < number_of_digits(number as nat));
            }
            temp = temp / 10;
            count = count + 1;
        }
        
        proof {
            assert(temp == 0);
            assert(count == number_of_digits(number as nat));
        }
        count
    };
    
    if ndigits == 0 {
        proof {
            assert(false); // ndigits is always at least 1
        }
        return 0;
    }
    
    if number == 0 {
        proof {
            assert(sum_digits(0) == sum_digits_recursive(0, power10(0)));
            assert(sum_digits_recursive(0, 1) == 0);
        }
        return 0;
    }
    
    let mut power: u64 = 1;
    let mut i: u64 = 1;
    
    while i < ndigits
        invariant
            1 <= i <= ndigits,
            ndigits == number_of_digits(number as nat),
            power == power10((i - 1) as nat),
            power <= u64::MAX / 10 || i == ndigits,
        decreases ndigits - i
    {
        proof {
            lemma_power10_positive((i - 1) as nat);
            assert(power10(i as nat) == 10 * power10((i - 1) as nat));
            lemma_number_of_digits_bounds(number as nat);
            assert(number < power10(ndigits as nat));
            if i < ndigits - 1 {
                lemma_power10_monotonic(i as nat, (ndigits - 2) as nat);
                lemma_power10_monotonic((ndigits - 2) as nat, (ndigits - 1) as nat);
            }
        }
        power = power * 10;
        i = i + 1;
    }
    
    proof {
        assert(i == ndigits);
        assert(power == power10((ndigits - 1) as nat));
        lemma_power10_positive((ndigits - 1) as nat);
        lemma_number_of_digits_bounds(number as nat);
    }
    
    while remaining > 0 && power > 0
        invariant
            power == 0 || power <= power10((ndigits - 1) as nat),
            remaining <= number,
            sum <= number,
            (power == 0 && remaining > 0) ==> false,
            sum + sum_digits_recursive(remaining as nat, power as nat) == sum_digits(number as nat),
        decreases power
    {
        let digit = remaining / power;
        proof {
            lemma_number_of_digits_bounds(number as nat);
            assert(number < power10(ndigits as nat));
            assert(remaining <= number);
            assert(remaining < power10(ndigits as nat));
            if power == power10((ndigits - 1) as nat) {
                assert(remaining < 10 * power);
            } else {
                assert(remaining < power * 10);
            }
            lemma_digit_bound(remaining as nat, power as nat);
            assert(digit <= 9);
            
            lemma_sum_digits_bound(number as nat);
            assert(sum_digits(number as nat) <= number);
            assert(sum + sum_digits_recursive(remaining as nat, power as nat) == sum_digits(number as nat));
            lemma_sum_digits_recursive_bound(remaining as nat, power as nat);
            assert(sum_digits_recursive(remaining as nat, power as nat) <= remaining);
            assert(sum + sum_digits_recursive(remaining as nat, power as nat) <= number);
            assert(digit <= remaining / power);
            assert(sum + digit <= sum + sum_digits_recursive(remaining as nat, power as nat));
            assert(sum + digit <= number);
        }
        sum = sum + digit;
        let old_remaining = remaining;
        remaining = remaining % power;
        
        proof {
            assert(old_remaining == digit * power + remaining);
            lemma_sum_digits_recursive_step(old_remaining as nat, power as nat);
            assert(sum_digits_recursive(old_remaining as nat, power as nat) 
                   == (digit as nat) + sum_digits_recursive(remaining as nat, (power/10) as nat));
        }
        
        power = power / 10;
    }
    
    proof {
        assert(remaining == 0 || power == 0);
        if power == 0 {
            assert(sum_digits_recursive(remaining as nat, 0) == 0);
        }
        if remaining == 0 {
            assert(sum_digits_recursive(0, power as nat) == 0);
        }
        assert(sum == sum_digits(number as nat));
    }
    
    sum
}
// </vc-code>

fn main() {}

}