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
/* helper modified by LLM (iteration 5): Added decreases clause to recursive function for bounds on even palindrome count */
proof fn count_even_bound(n: nat)
    ensures
        count_even_palindromes_in_range(1, n) <= n,
    decreases n
{
    if n == 0 {
        assert(count_even_palindromes_in_range(1, 0) == 0);
        assert(0 <= 0);
    } else {
        count_even_bound((n - 1) as nat);
        let prev_count = count_even_palindromes_in_range(1, (n - 1) as nat);
        let curr_count = count_even_palindromes_in_range(1, n);
        assert(curr_count <= prev_count + 1);
        assert(prev_count <= n - 1);
    }
}
/* helper modified by LLM (iteration 5): Added decreases clause to recursive function for bounds on odd palindrome count */
proof fn count_odd_bound(n: nat)
    ensures
        count_odd_palindromes_in_range(1, n) <= n,
    decreases n
{
    if n == 0 {
        assert(count_odd_palindromes_in_range(1, 0) == 0);
    } else {
        count_odd_bound((n - 1) as nat);
        let prev_count = count_odd_palindromes_in_range(1, (n - 1) as nat);
        let curr_count = count_odd_palindromes_in_range(1, n);
        assert(curr_count <= prev_count + 1);
    }
}
/* helper modified by LLM (iteration 5): Added decreases clause to recursive function for sum of even and odd palindrome counts */
proof fn palindromes_sum(n: nat)
    ensures
        count_palindromes_in_range(1, n) == count_even_palindromes_in_range(1, n) + count_odd_palindromes_in_range(1, n),
    decreases n
{
    if n == 0 {
        assert(count_palindromes_in_range(1, 0) == 0);
        assert(count_even_palindromes_in_range(1, 0) == 0);
        assert(count_odd_palindromes_in_range(1, 0) == 0);
    } else {
        palindromes_sum((n - 1) as nat);
        let total_pal = count_palindromes_in_range(1, n);
        let even_pal = count_even_palindromes_in_range(1, n);
        let odd_pal = count_odd_palindromes_in_range(1, n);
        assert(total_pal == even_pal + odd_pal);
    }
}
/* helper modified by LLM (iteration 5): Executable palindrome check function */
fn is_palindrome_exec(num: u32) -> bool {
    if num == 0 {
        true
    } else {
        let mut reversed = 0;
        let mut original = num;
        while original > 0 {
            reversed = reversed * 10 + (original % 10);
            original /= 10;
        }
        reversed == num
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
/* code modified by LLM (iteration 5): Iterative count of even and odd palindromes using while loop */
{
    let mut even_count = 0u32;
    let mut odd_count = 0u32;
    let mut i = 1u32;
    while i <= n {
        if is_palindrome_exec(i) {
            if i % 2 == 0 {
                even_count += 1;
            } else {
                odd_count += 1;
            }
        }
        i += 1;
    }
    (even_count, odd_count)
}
// </vc-code>


}

fn main() {}