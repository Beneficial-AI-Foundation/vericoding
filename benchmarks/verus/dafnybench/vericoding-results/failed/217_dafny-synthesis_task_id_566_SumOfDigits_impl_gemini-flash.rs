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
spec fn number_of_digits_u64(n: u64) -> u64
    decreases n
{
    if n <= 9 { 1 } else { (1 + number_of_digits_u64(n / 10)) as u64 }
}

spec fn power10_u64(n: u64) -> u64
    decreases n
{
    if n == 0 { 1 } else { (10 * power10_u64((n - 1) as u64)) as u64 }
}

proof fn lemma_number_of_digits_u64_is_same_as_nat(n: u64)
    ensures number_of_digits_u64(n) == number_of_digits(n as nat)
    decreases n
{
    if n <= 9 {
        assert(number_of_digits_u64(n) == 1);
        assert(number_of_digits(n as nat) == 1);
    } else {
        lemma_number_of_digits_u64_is_same_as_nat(n/10);
        assert(number_of_digits_u64(n) == (1 + number_of_digits_u64(n/10)) as u64);
        assert(number_of_digits(n as nat) == (1 + number_of_digits((n as nat)/10)) as nat);
    }
}

proof fn lemma_power10_u64_is_same_as_nat(n: u64)
    ensures power10_u64(n) == power10(n as nat)
    decreases n
{
    if n == 0 {
        assert(power10_u64(n) == 1);
        assert(power10(n as nat) == 1);
    } else {
        lemma_power10_u64_is_same_as_nat((n - 1) as u64);
        assert(power10_u64(n) == (10 * power10_u64((n - 1) as u64)) as u64);
        assert(power10(n as nat) == (10 * power10(((n - 1) as u64) as nat)) as nat);
    }
}

spec fn sum_of_digits_recursive_u64(n: u64, p: u64) -> u64
    decreases p
{
    if n == 0 || p == 0 { 0 }
    else {
        let left_most_digit = n / p;
        let rest = n % p;
        (left_most_digit + sum_of_digits_recursive_u64(rest, p / 10)) as u64
    }
}

proof fn lemma_sum_digits_recursive_equivalence(n: u64, p: u64)
    requires
        p >= 1,
    ensures
        sum_digits_recursive(n as nat, p as nat) == sum_of_digits_recursive_u64(n, p)
    decreases p
{
    if n == 0 || p == 0 {
    } else {
        let left_most_digit_nat = (n as nat) / (p as nat);
        let rest_nat = (n as nat) % (p as nat);
        let left_most_digit_u64 = n / p;
        let rest_u64 = n % p;

        assert(left_most_digit_nat == left_most_digit_u64 as nat);
        assert(rest_nat == rest_u64 as nat);

        if p / 10 > 0 {
            lemma_sum_digits_recursive_equivalence(rest_u64, p / 10);
        } else {
            assert(sum_of_digits_recursive_u64(rest_u64, 0) == 0);
            assert(sum_digits_recursive(rest_nat, 0) == 0);
        }
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
    let mut num = number;
    let mut sum: u64 = 0;

    if num == 0 {
        return 0;
    }

    let mut num_digits: u64 = 0; 
    let mut temp_num = num;
    proof {
        lemma_number_of_digits_u64_is_same_as_nat(temp_num);
    }
    while temp_num > 0
        invariant
            temp_num >= 0,
            num_digits <= number_of_digits_u64(number),
            temp_num == number / power10_u64(num_digits),
            num_digits >= 0,
        decreases temp_num
    {
        temp_num /= 10;
        num_digits += 1;
    }

    assert(num_digits == number_of_digits_u64(number));
    proof { lemma_number_of_digits_u64_is_same_as_nat(number); }

    let mut p = 1u64;
    if num_digits > 0 {
        let mut i = 0u64;
        proof { lemma_power10_u64_is_same_as_nat(0); }
        while i < num_digits - 1
            invariant
                p == power10_u64(i),
                i <= num_digits - 1,
                power10_u64(i) == power10(i as nat),
            decreases (num_digits - 1) - i
        {
            p *= 10;
            i += 1;
            proof {
                lemma_power10_u64_is_same_as_nat(i);
            }
        }
    } else {
        p = 0; // This case only happens if num_digits is 0. But num is >= 0, so num_digits must be 1 at least.
         // In this specific task, number is u64 which should always have at least 1 digit (0 has 1 digit).
    }
    
    assert(p == power10_u64(number_of_digits_u64(number).checked_sub(1).unwrap_or(0)));
    proof {
        if number > 0 {
            lemma_power10_u64_is_same_as_nat(number_of_digits_u64(number).checked_sub(1).unwrap_or(0));
            assert(power10_u64(number_of_digits_u64(number).checked_sub(1).unwrap_or(0)) == power10((number_of_digits_u64(number).checked_sub(1).unwrap_or(0)) as nat));
            assert(num_digits == number_of_digits_u64(number));
            assert(number_of_digits_u64(number) == number_of_digits(number as nat));
        } else {
            // number == 0, num_digits == 1
            assert(num_digits == 1); 
            assert(number_of_digits_u64(0) == 1);
            lemma_power10_u64_is_same_as_nat(0);
            assert(p == power10_u64(0));
        }
    }

    let initial_p = p;
    let initial_num = number;

    while p > 0
        invariant
            num >= 0,
            p >= 0,
            initial_p >= p,
            initial_num >= num,
            sum + sum_of_digits_recursive_u64(num, p) == sum_of_digits_recursive_u64(initial_num, initial_p),
            initial_p == power10_u64(number_of_digits_u64(initial_num).checked_sub(1).unwrap_or(0)),
            p >= 1 ==> sum_digits_recursive(num as nat, p as nat) == sum_of_digits_recursive_u64(num, p),

        decreases p
    {
        proof {
            if p >= 1 {
                lemma_sum_digits_recursive_equivalence(num, p);
            }
            if p / 10 > 0 {
                lemma_sum_digits_recursive_equivalence(num % p, p / 10);
            }
        }
        let digit = num / p;
        sum += digit;
        num %= p;
        p /= 10;
    }

    proof {
        if number > 0 {
            assert(initial_p == power10_u64(number_of_digits_u64(number).checked_sub(1).unwrap_or(0)));
            lemma_sum_digits_recursive_equivalence(number, initial_p);
            assert(sum_of_digits_recursive_u64(initial_num, initial_p) == sum_digits_recursive(number as nat, initial_p as nat));
            assert(number_of_digits_u64(number) == number_of_digits(number as nat));
            assert(initial_p as nat == power10((number_of_digits(number as nat) - 1) as nat));
            assert(sum_digits(number as nat) == sum_digits_recursive(number as nat, power10((number_of_digits(number as nat) - 1) as nat)));
            assert(sum + sum_of_digits_recursive_u64(num, p) == sum_of_digits_recursive_u64(initial_num, initial_p));
            assert(p == 0); 
            assert(sum_of_digits_recursive_u64(num, p) == 0); 
            assert(sum == sum_of_digits_recursive_u64(initial_num, initial_p));
            assert(sum == sum_digits(initial_num as nat));
            assert(sum == sum_digits(number as nat)); 
        } else {
            assert(sum == 0);
            assert(sum_digits(0) == 0);
        }
    }

    sum
}
// </vc-code>

fn main() {}

}