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
/* code modified by LLM (iteration 5): [Fixed the type cast issue where a `u32` value was explicitly cast to `nat` before being passed to `is_palindrome`, instead, removing the explicit cast as `is_palindrome` already accepts `nat` which `u32` can coerce to.] */
{
    let mut current: u32 = 1;
    let mut even_count: u32 = 0;
    let mut odd_count: u32 = 0;

    while current <= n
        invariant 
            1 <= current,
            current <= n + 1,
            even_count as nat == count_even_palindromes_in_range(1, (current - 1) as nat),
            odd_count as nat == count_odd_palindromes_in_range(1, (current - 1) as nat),
            even_count as nat + odd_count as nat == count_palindromes_in_range(1, (current - 1) as nat)
        decreases n as int - current as int
    {
        // We need to prove `is_palindrome` for `current` before calling it in if condition
        // The `is_palindrome` function itself contains the properties required for `even_count` and `odd_count`
        
        if current <= n {
            let current_nat = current as nat;
            if is_palindrome(current_nat) {
                if current % 2 == 0 {
                    even_count = even_count + 1;
                } else {
                    odd_count = odd_count + 1;
                }
            }
        }
       
        current = current + 1;
    }

    proof {
        assert(current == n + 1);
        lemma_counts_accumulated_correctly(n, current, even_count, odd_count);
        assert(count_even_palindromes_in_range(1, n as nat) == even_count as nat);
        assert(count_odd_palindromes_in_range(1, n as nat) == odd_count as nat);
    }

    (even_count, odd_count)
}
// </vc-code>


}

fn main() {}