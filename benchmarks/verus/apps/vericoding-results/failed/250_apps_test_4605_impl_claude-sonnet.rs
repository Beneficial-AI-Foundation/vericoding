// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: int, b: int) -> bool {
    n >= 1 && a >= 1 && a <= b && b <= 36
}

spec fn digit_sum(n: int) -> int 
    decreases n
{
    if n <= 0 { 0 }
    else { (n % 10) + digit_sum(n / 10) }
}

spec fn sum_in_range(n: int, a: int, b: int) -> int
    decreases n
{
    if n <= 0 { 0 }
    else if a <= digit_sum(n) && digit_sum(n) <= b { 
        n + sum_in_range(n - 1, a, b) 
    }
    else { 
        sum_in_range(n - 1, a, b) 
    }
}
// </vc-preamble>

// <vc-helpers>
fn digit_sum_impl(n: i8) -> (result: i8)
    requires n >= 0
    ensures result as int == digit_sum(n as int),
            result >= 0
    decreases n
{
    if n == 0 {
        0
    } else {
        let digit = n % 10;
        let rest = digit_sum_impl(n / 10);
        assert(digit >= 0 && digit <= 9);
        assert(rest >= 0);
        assert(digit + rest >= 0 && digit + rest <= 18); // max for n=127 is 1+2+7=10
        digit + rest
    }
}

/* helper modified by LLM (iteration 5): fixed lemma syntax */
proof fn lemma_digit_sum_nonneg(n: int)
    requires n >= 0
    ensures digit_sum(n) >= 0
    decreases n
{
    if n > 0 {
        lemma_digit_sum_nonneg(n / 10);
    }
}

proof fn lemma_sum_in_range_nonneg(n: int, a: int, b: int)
    requires n >= 0
    ensures sum_in_range(n, a, b) >= 0
    decreases n
{
    if n > 0 {
        lemma_sum_in_range_nonneg(n - 1, a, b);
    }
}

proof fn lemma_sum_bound(n: int, a: int, b: int)
    requires n >= 0 && n <= 127
    ensures sum_in_range(n, a, b) <= 127 * 128 / 2
    decreases n
{
    if n > 0 {
        lemma_sum_bound(n - 1, a, b);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8, b: i8) -> (result: i8)
    requires valid_input(n as int, a as int, b as int)
    ensures 
        result as int == sum_in_range(n as int, a as int, b as int) &&
        result >= 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed overflow bounds with proper preconditions */
    proof {
        lemma_sum_in_range_nonneg(n as int, a as int, b as int);
        lemma_sum_bound(n as int, a as int, b as int);
    }
    
    let mut i = 1i8;
    let mut total = 0i8;
    
    while i <= n
        invariant
            1 <= i <= n + 1,
            total as int == sum_in_range((i - 1) as int, a as int, b as int),
            total >= 0,
            total <= 127
        decreases (n - i) as nat
    {
        let ds = digit_sum_impl(i);
        
        proof {
            lemma_digit_sum_nonneg(i as int);
        }
        
        if a <= ds && ds <= b {
            assert(i <= n);
            assert(n <= 127);
            assert(total <= 127);
            assert(i >= 1);
            total = total + i;
        }
        
        assert(i < n + 1);
        assert(i <= 127);
        i = i + 1;
    }
    
    total
}
// </vc-code>


}

fn main() {}