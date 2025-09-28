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
proof fn lemma_count_range_split(start: nat, mid: nat, end: nat)
    requires start <= mid + 1 <= end + 1,
    ensures
        count_palindromes_in_range(start, end) == count_palindromes_in_range(start, mid) + count_palindromes_in_range(mid + 1, end),
        count_even_palindromes_in_range(start, end) == count_even_palindromes_in_range(start, mid) + count_even_palindromes_in_range(mid + 1, end),
        count_odd_palindromes_in_range(start, end) == count_odd_palindromes_in_range(start, mid) + count_odd_palindromes_in_range(mid + 1, end),
    decreases end - start
{
    if start <= mid {
        lemma_count_range_split(start + 1, mid, end);
    }
}

proof fn lemma_even_odd_sum(start: nat, end: nat)
    requires start <= end + 1,
    ensures
        count_palindromes_in_range(start, end) ==
        count_even_palindromes_in_range(start, end) + count_odd_palindromes_in_range(start, end),
    decreases end - start
{
    if start <= end {
        lemma_even_odd_sum(start + 1, end);
    }
}

/* helper modified by LLM (iteration 3): fixed map closure signature to include index */
fn exec_digits_of(n: u32) -> (result: Vec<u32>)
    requires
        n >= 1,
    ensures
        result.view().map(|_i: int, x: u32| x as nat) == digits_of(n as nat),
    decreases n
{
    if n < 10 {
        vec![n]
    } else {
        let mut prefix = exec_digits_of(n / 10);
        prefix.push(n % 10);
        prefix
    }
}

/* helper modified by LLM (iteration 5): fixed slicing compilation error using Vec::split_at */
fn exec_reverse_vec(v: Vec<u32>) -> (result: Vec<u32>)
    ensures
        result.len() == v.len(),
        result.view().map(|_i: int, x: u32| x as nat) == reverse_seq(v.view().map(|_i: int, x: u32| x as nat)),
    decreases v.len()
{
    if v.len() <= 1 {
        v
    } else {
        let (mut first_vec, rest_v) = v.split_at(1);
        let first = first_vec.remove(0);
        let mut rest_rev = exec_reverse_vec(rest_v);
        rest_rev.push(first);
        rest_rev
    }
}

fn exec_is_palindrome(n: u32) -> (b: bool)
    requires n >= 1,
    ensures b == is_palindrome(n as nat),
{
    let digits = exec_digits_of(n);
    let reversed_digits = exec_reverse_vec(digits.clone());
    digits == reversed_digits
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
    /* code modified by LLM (iteration 5): No changes needed, fixing compilation error in helper function. */
    let mut i: u32 = 1;
    let mut even_count: u32 = 0;
    let mut odd_count: u32 = 0;

    while i <= n
        invariant
            1 <= i <= n + 1,
            even_count == count_even_palindromes_in_range(1, (i - 1) as nat),
            odd_count == count_odd_palindromes_in_range(1, (i - 1) as nat),
        decreases n - i
    {
        proof {
            lemma_count_range_split(1, (i - 1) as nat, i as nat);
        }

        if exec_is_palindrome(i) {
            if i % 2 == 0 {
                even_count = even_count + 1;
            } else {
                odd_count = odd_count + 1;
            }
        }
        i = i + 1;
    }

    proof {
        lemma_even_odd_sum(1, n as nat);
    }
    
    (even_count, odd_count)
}

// </vc-code>


}

fn main() {}