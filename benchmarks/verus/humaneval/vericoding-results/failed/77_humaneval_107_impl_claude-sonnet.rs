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
/* helper modified by LLM (iteration 5): complete palindrome check without overflow */
fn is_palindrome_impl(num: u32) -> (result: bool)
    ensures
        result == is_palindrome(num as nat),
{
    if num == 0 {
        return true;
    }
    
    let mut n = num;
    let mut reversed = 0u32;
    let original = num;
    
    while n > 0
        invariant
            n <= num,
            reversed <= u32::MAX / 10,
        decreases n
    {
        let digit = n % 10;
        if reversed > (u32::MAX - digit) / 10 {
            proof {
                assert(reversed * 10 + digit > u32::MAX);
                assert(false);
            }
        }
        reversed = reversed * 10 + digit;
        n = n / 10;
    }
    
    original == reversed
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
    /* code modified by LLM (iteration 5): fixed overflow bounds and postcondition */
    let mut current = 1u32;
    let mut even_count = 0u32;
    let mut odd_count = 0u32;
    
    while current <= n
        invariant
            current >= 1,
            current <= n + 1,
            even_count <= n,
            odd_count <= n,
            even_count == count_even_palindromes_in_range(1, (current - 1) as nat),
            odd_count == count_odd_palindromes_in_range(1, (current - 1) as nat),
        decreases n - current
    {
        if is_palindrome_impl(current) {
            if current % 2 == 0 {
                if even_count < u32::MAX {
                    even_count = even_count + 1;
                }
            } else {
                if odd_count < u32::MAX {
                    odd_count = odd_count + 1;
                }
            }
        }
        if current < u32::MAX {
            current = current + 1;
        } else {
            break;
        }
    }
    
    (even_count, odd_count)
}
// </vc-code>


}

fn main() {}