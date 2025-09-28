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
spec fn is_power10(n: nat) -> bool
{
    if n == 1 { true }
    else if n % 10 == 0 { is_power10(n/10) }
    else { false }
}

spec fn log10_of_power(mut p: nat) -> nat
    requires p > 0 && is_power10(p)
    decreases p
{
    if p == 1 { 0 } else { 1 + log10_of_power(p/10) }
}

proof fn lemma_power10_is_power10(k: nat)
    ensures is_power10(power10(k))
    decreases k
{
    if k == 0 {
        // power10(0) == 1
    } else {
        lemma_power10_is_power10(k - 1);
        // power10(k) = 10 * power10(k-1) so is_power10 holds
    }
}

proof fn lemma_log10_of_power_correct(p: nat)
    requires p > 0 && is_power10(p)
    ensures power10(log10_of_power(p)) == p
    decreases p
{
    if p == 1 {
        // log10_of_power(1) == 0, power10(0) == 1 == p
    } else {
        lemma_log10_of_power_correct(p/10);
        // power10(log10_of_power(p)) = 10 * power10(log10_of_power(p/10)) == 10 * (p/10) == p
    }
}

proof fn lemma_lt_le_sub1(a: nat, b: nat)
    requires a < b
    ensures a <= b - 1
    decreases b
{
    if b == 0 {
    } else {
        // trivial by arithmetic
    }
}

proof fn lemma_power10_bounds_positive(n: nat)
    requires n > 0
    ensures (
        {
            let q = power10((number_of_digits(n) - 1) as nat);
            q <= n && n < 10 * q
        }
    )
    decreases n
{
    if n <= 9 {
        // number_of_digits(n) == 1
        // q = power10(0) = 1
        // 1 <= n <= 9 implies 1 <= n and n < 10
    } else {
        let m = (n / 10) as nat;
        // apply inductive hypothesis to m (> = 0)
        lemma_power10_bounds_positive(m);
        // number_of_digits(n) = 1 + number_of_digits(m) for n > 9
        proof {
            // by definition of number_of_digits this holds
            assert(number_of_digits(n) == 1 + number_of_digits(m));
        }
        let qm = power10((number_of_digits(m) - 1) as nat);
        let q = power10((number_of_digits(n) - 1) as nat);
        // number_of_digits(n)-1 == number_of_digits(m)
        assert((number_of_digits(n) - 1) as nat == number_of_digits(m));
        // thus q == 10 * qm
        assert(q == 10 * qm);
        // from lemma on m: qm <= m && m < 10 * qm
        assert(qm <= m);
        assert(m < 10 * qm);
        // show q <= n: q = 10*qm <= 10*m <= n (since n = 10*m + r, r>=0)
        assert(10 * qm <= 10 * m);
        assert(10 * m <= n);
        assert(q <= n);
        // show n < 10*q: 10*q = 100*qm; from m < 10*qm we get m <= 10*qm - 1
        lemma_lt_le_sub1(m, 10 * qm);
        assert(m <= 10 * qm - 1);
        // multiply by 10: 10*m <= 100*qm - 10
        assert(10 * m <= 100 * qm - 10);
        // then 10*m + 9 <= 100*qm - 1 < 100*qm
        assert(10 * m + 9 < 100 * qm);
        // n = 10*m + r with r <= 9, so n <= 10*m + 9 < 100*qm = 10*q
        assert(n < 10 * q);
    }
}

proof fn lemma_power10_ge(i: nat, j: nat)
    requires j > i
    ensures power10(j) >= 10 * power10(i)
    decreases j - i
{
    if j == i + 1 {
        // power10(i+1) == 10 * power10(i)
    } else {
        lemma_power10_ge(i, j - 1);
        // power10(j) = 10 * power10(j-1) >= 10 * (10 * power10(i)) >= 10 * power10(i)
    }
}

proof fn lemma_powers_unique(p: nat, q: nat, n: nat)
    requires
        p > 0 && q > 0,
        is_power10(p),
        is_power10(q),
        p <= n && n < 10 * p,
        q <= n && n < 10 * q,
    ensures p == q
    decreases n
{
    lemma_log10_of_power_correct(p);
    lemma_log10_of_power_correct(q);
    let i = log10_of_power(p);
    let j = log10_of_power(q);
    if i < j {
        lemma_power10_ge(i, j);
        assert(power10(j) >= 10 * power10(i));
        assert(q >= 10 * p);
        assert(q <= n);
        assert(n < 10 * p);
        assert(false);
    } else if j < i {
        lemma_power10_ge(j, i);
        assert(power10(i) >= 10 * power10(j));
        assert(p >= 10 * q);
        assert(p <= n);
        assert(n < 10 * q);
        assert(false);
    } else {
        // i == j implies p == q
    }
}

proof fn lemma_number_of_digits_div10(n: nat)
    requires n > 9
    ensures number_of_digits(n) == 1 + number_of_digits((n/10) as nat)
    decreases n
{
    // by the definition of number_of_digits this holds
}

proof fn lemma_power10_succ(i: nat)
    ensures power10(i + 1) == 10 * power10(i)
    decreases i
{
    if i == 0 {
        // power10(1) == 10 * power10(0)
    } else {
        lemma_power10_succ(i - 1);
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
    if number == 0 {
        return 0;
    }

    // compute k = number_of_digits(number)-1, then p = 10^k by looping k times
    let k: u64 = (number_of_digits(number as nat) - 1) as u64;
    let mut p: u64 = 1;
    let mut i: u64 = 0;
    while i < k
        invariant i <= k;
        invariant is_power10((p as nat));
        invariant (p as nat) == power10(i as nat);
        decreases k - i;
    {
        let p_old = p;
        let i_old = i;
        let p_new = p_old * 10;
        let i_new = i_old + 1;
        proof {
            assert((p_old as nat) == power10(i_old as nat));
            lemma_power10_succ(i_old as nat);
            assert((p_new as nat) == power10(i_new as nat));
        }
        p = p_new;
        i = i_new;
    }

    proof {
        // after the loop i == k and p == power10(k)
        assert(i == k);
        assert((p as nat) == power10((k as nat)));
        // relate to sum_digits spec
        assert(sum_digits_recursive(number as nat, p as nat) == sum_digits(number as nat));
    }

    // Now perform left-most digit extraction matching sum_digits_recursive
    let mut n = number;
    let mut acc: u64 = 0;

    // invariant: acc as nat + sum_digits_recursive(n as nat, p as nat) == sum_digits(number as nat)
    while p > 0
        invariant acc as nat + sum_digits_recursive(n as nat, p as nat) == sum_digits(number as nat);
        decreases (p as nat);
    {
        let lm = n / p;
        let rest = n % p;
        proof {
            assert(sum_digits_recursive(n as nat, p as nat) ==
                   (lm as nat) + sum_digits_recursive(rest as nat, (p/10) as nat));
        }
        acc = acc + lm;
        n = rest;
        p = p / 10;
    }

    return acc;
}
// </vc-code>

fn main() {}

}