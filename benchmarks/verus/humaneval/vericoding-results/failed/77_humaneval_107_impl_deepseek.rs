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

    /* helper modified by LLM (iteration 5): Fixed return type syntax for proof function */
    proof fn count_palindromes_helper_lemma(n: nat, current: nat, even_count: nat, odd_count: nat) -> (even_res: nat, odd_res: nat)
        requires
            n >= 1,
            current >= 1,
            current <= n + 1,
        ensures
            even_res == count_even_palindromes_in_range(current, n) + even_count,
            odd_res == count_odd_palindromes_in_range(current, n) + odd_count,
        decreases n - current + 1
    {
        if current > n {
            (even_count, odd_count)
        } else {
            if is_palindrome(current) {
                if current % 2 == 0 {
                    count_palindromes_helper_lemma(n, current + 1, even_count + 1, odd_count)
                } else {
                    count_palindromes_helper_lemma(n, current + 1, even_count, odd_count + 1)
                }
            } else {
                count_palindromes_helper_lemma(n, current + 1, even_count, odd_count)
            }
        }
    }

    /* helper modified by LLM (iteration 5): Added spec function to verify spec and proof function consistency */
    spec fn count_palindromes_helper_spec_equals_spec_fns(n: nat, current: nat, even_count: nat, odd_count: nat) -> bool {
        let (helper_even, helper_odd) = count_palindromes_helper(n, current, even_count, odd_count);
        helper_even == count_even_palindromes_in_range(current, n) + even_count &&
        helper_odd == count_odd_palindromes_in_range(current, n) + odd_count
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
    /* code modified by LLM (iteration 5): Fixed implementation with proper lemma application */
    let n_nat: nat = n as nat;
    proof {
        let (even_val, odd_val) = count_palindromes_helper_lemma(n_nat, 1, 0, 0);
        assert(even_val == count_even_palindromes_in_range(1, n_nat)) by {
            assert(count_even_palindromes_in_range(1, n_nat) + 0 == count_even_palindromes_in_range(1, n_nat));
        }
        assert(odd_val == count_odd_palindromes_in_range(1, n_nat)) by {
            assert(count_odd_palindromes_in_range(1, n_nat) + 0 == count_odd_palindromes_in_range(1, n_nat));
        }
        assert(count_palindromes_helper_spec_equals_spec_fns(n_nat, 1, 0, 0)) by {
            assert(count_palindromes_helper(n_nat, 1, 0, 0).0 == count_even_palindromes_in_range(1, n_nat));
            assert(count_palindromes_helper(n_nat, 1, 0, 0).1 == count_odd_palindromes_in_range(1, n_nat));
        }
    }
    let (even, odd) = count_palindromes_helper(n_nat, 1, 0, 0);
    (even as u32, odd as u32)
}
// </vc-code>


}

fn main() {}