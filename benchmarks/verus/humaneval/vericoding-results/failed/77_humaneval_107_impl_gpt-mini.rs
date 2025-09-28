// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: nat) -> bool {
    n >= 1
}

spec fn digits_of(n: nat) -> Seq<nat>
    decreases n
{
    if n < 10 {
        seq![n]
    } else {
        digits_of(n / 10).push(n % 10)
    }
}

spec fn reverse_seq<T>(s: Seq<T>) -> Seq<T>
    decreases s.len()
{
    if s.len() <= 1 {
        s
    } else {
        reverse_seq(s.subrange(1, s.len() as int)).push(s[0])
    }
}

spec fn is_palindrome(n: nat) -> bool {
    let digits = digits_of(n);
    digits == reverse_seq(digits)
}

spec fn count_palindromes_in_range(start: nat, end: nat) -> nat
    decreases end - start + 1
{
    if start > end {
        0
    } else if is_palindrome(start) {
        1 + count_palindromes_in_range(start + 1, end)
    } else {
        count_palindromes_in_range(start + 1, end)
    }
}

spec fn count_even_palindromes_in_range(start: nat, end: nat) -> nat
    decreases end - start + 1
{
    if start > end {
        0
    } else if is_palindrome(start) && start % 2 == 0 {
        1 + count_even_palindromes_in_range(start + 1, end)
    } else {
        count_even_palindromes_in_range(start + 1, end)
    }
}

spec fn count_odd_palindromes_in_range(start: nat, end: nat) -> nat
    decreases end - start + 1
{
    if start > end {
        0
    } else if is_palindrome(start) && start % 2 == 1 {
        1 + count_odd_palindromes_in_range(start + 1, end)
    } else {
        count_odd_palindromes_in_range(start + 1, end)
    }
}
spec fn count_palindromes_helper(n: nat, current: nat, even_count: nat, odd_count: nat) -> (nat, nat)
    decreases n - current + 1
{
    if current > n {
        (even_count, odd_count)
    } else if is_palindrome(current) {
        if current % 2 == 0 {
            count_palindromes_helper(n, current + 1, even_count + 1, odd_count)
        } else {
            count_palindromes_helper(n, current + 1, even_count, odd_count + 1)
        }
    } else {
        count_palindromes_helper(n, current + 1, even_count, odd_count)
    }
}

// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): proof relating recursive helper to range count functions */
proof fn count_palindromes_helper_spec(n: nat, current: nat, even_count: nat, odd_count: nat)
    requires
        current >= 1,
    ensures
        count_palindromes_helper(n, current, even_count, odd_count) == (even_count + count_even_palindromes_in_range(current, n), odd_count + count_odd_palindromes_in_range(current, n)),
    decreases
        n - current + 1
{
    if current > n {
        // base case: both range counts are 0 and helper returns (even_count, odd_count)
    } else {
        if is_palindrome(current) {
            if current % 2 == 0 {
                // even palindrome: advance even_count
                count_palindromes_helper_spec(n, current + 1, even_count + 1, odd_count);
            } else {
                // odd palindrome: advance odd_count
                count_palindromes_helper_spec(n, current + 1, even_count, odd_count + 1);
            }
        } else {
            // not a palindrome: counts unchanged
            count_palindromes_helper_spec(n, current + 1, even_count, odd_count);
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn even_odd_palindrome(n: u32) -> (result: (u32, u32))
    requires 
        n >= 1
    ensures 
        result.0 >= 0,
        result.1 >= 0,
        result.0 == count_even_palindromes_in_range(1, n as nat),
        result.1 == count_odd_palindromes_in_range(1, n as nat),
        result.0 + result.1 == count_palindromes_in_range(1, n as nat),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): iterative loop counting palindromes into even/odd counters */
    let N: nat = n as nat;
    let mut i: nat = 1;
    let mut even: nat = 0;
    let mut odd: nat = 0;

    while i <= N
        invariant
            even == count_even_palindromes_in_range(1, i - 1),
            odd == count_odd_palindromes_in_range(1, i - 1),
        decreases
            N - i + 1
    {
        if is_palindrome(i) {
            if i % 2 == 0 {
                even = even + 1;
            } else {
                odd = odd + 1;
            }
        }
        i = i + 1;
    }

    (even as u32, odd as u32)
}

// </vc-code>


}

fn main() {}