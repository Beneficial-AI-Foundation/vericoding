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
/* helper modified by LLM (iteration 4): Added trigger annotation for quantifier */
fn is_palindrome_exec(n: u32) -> (result: bool)
    ensures
        result == is_palindrome(n as nat)
{
    if n == 0 {
        return true;
    }
    
    let mut digits = Vec::new();
    let mut temp = n;
    
    // Collect digits in reverse order (least significant first)
    while temp > 0
        invariant
            temp >= 0
        decreases temp
    {
        digits.push((temp % 10) as u32);
        temp = temp / 10;
    }
    
    // Now check if the digits form a palindrome
    let len = digits.len();
    if len == 0 {
        return true;
    }
    
    let mut i: usize = 0;
    
    while i < len / 2
        invariant
            0 <= i <= len / 2,
            len == digits.len(),
            forall|j: int| #[trigger] (0 <= j < i) ==> digits@[j] == digits@[len - 1 - j]
        decreases (len / 2) - i
    {
        // Since we collected digits in reverse, compare from both ends
        let left_idx = i;
        let right_idx = len - 1 - i;
        
        assert(0 <= left_idx < len);
        assert(0 <= right_idx < len);
        
        if digits[left_idx] != digits[right_idx] {
            return false;
        }
        i = i + 1;
    }
    
    true
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
    /* code modified by LLM (iteration 4): No changes needed to main code */
    let mut even_count: u32 = 0;
    let mut odd_count: u32 = 0;
    let mut current: u32 = 1;
    
    while current <= n
        invariant
            1 <= current,
            current <= n + 1,
            even_count == count_even_palindromes_in_range(1, (current - 1) as nat),
            odd_count == count_odd_palindromes_in_range(1, (current - 1) as nat),
            even_count + odd_count == count_palindromes_in_range(1, (current - 1) as nat),
            even_count <= n,
            odd_count <= n
        decreases n - current + 1
    {
        if is_palindrome_exec(current) {
            if current % 2 == 0 {
                assert(even_count < n);
                even_count = even_count + 1;
            } else {
                assert(odd_count < n);
                odd_count = odd_count + 1;
            }
        }
        assert(current < n + 1);
        current = current + 1;
    }
    
    (even_count, odd_count)
}
// </vc-code>


}

fn main() {}