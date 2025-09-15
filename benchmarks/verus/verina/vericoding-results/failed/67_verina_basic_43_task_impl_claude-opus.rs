// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn sum_lemma(n: nat)
    ensures
        15 * sum_recursive(n) == n * (2 * n + 1) * (7 + 24 * (n * n * n) - 12 * (n * n) - 14 * n)
    decreases n
{
    if n == 0 {
        assert(sum_recursive(0) == 0);
        assert(15 * 0 == 0);
    } else {
        sum_lemma((n - 1) as nat);
        let prev = (n - 1) as nat;
        let odd = (2 * n - 1) as nat;
        assert(sum_recursive(n) == sum_recursive(prev) + odd * odd * odd * odd);
        
        let lhs = 15 * sum_recursive(n);
        let rhs = n * (2 * n + 1) * (7 + 24 * (n * n * n) - 12 * (n * n) - 14 * n);
        
        assert(odd * odd * odd * odd == (2 * n - 1) * (2 * n - 1) * (2 * n - 1) * (2 * n - 1));
        assert((2 * n - 1) * (2 * n - 1) == 4 * n * n - 4 * n + 1);
        assert((2 * n - 1) * (2 * n - 1) * (2 * n - 1) * (2 * n - 1) == 
               16 * n * n * n * n - 32 * n * n * n + 24 * n * n - 8 * n + 1);
        
        assert(15 * (odd * odd * odd * odd) == 
               15 * (16 * n * n * n * n - 32 * n * n * n + 24 * n * n - 8 * n + 1));
        
        if prev == 0 {
            assert(15 * sum_recursive(prev) == 0);
        } else {
            assert(15 * sum_recursive(prev) == 
                   prev * (2 * prev + 1) * (7 + 24 * (prev * prev * prev) - 12 * (prev * prev) - 14 * prev));
        }
        
        assert(lhs == rhs) by {
            assert(n * (2 * n + 1) * (7 + 24 * n * n * n - 12 * n * n - 14 * n) ==
                   48 * n * n * n * n * n + 24 * n * n * n * n - 24 * n * n * n * n
                   - 12 * n * n * n + 14 * n * n + 7 * n - 24 * n * n * n - 12 * n * n
                   - 14 * n * n - 7 * n);
            assert(n * (2 * n + 1) * (7 + 24 * n * n * n - 12 * n * n - 14 * n) ==
                   48 * n * n * n * n * n - 36 * n * n * n - 12 * n * n + 14 * n);
                   
            assert(prev * (2 * prev + 1) * (7 + 24 * prev * prev * prev - 12 * prev * prev - 14 * prev) ==
                   48 * prev * prev * prev * prev * prev - 36 * prev * prev * prev - 12 * prev * prev + 14 * prev);
        };
    }
}

spec fn sum_recursive(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else {
        let odd = (2 * n - 1) as nat;
        sum_recursive((n - 1) as nat) + odd * odd * odd * odd
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_of_fourth_power_of_odd_numbers(n: nat) -> (result: nat)
    ensures
        15 * result == n * (2 * n + 1) * (7 + 24 * (n * n * n) - 12 * (n * n) - 14 * n)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Return sum directly as u64 type, avoiding type casting issue */
{
    let mut sum: u64 = 0;
    let mut i: u64 = 0;
    
    while i < n
        invariant
            i <= n,
            sum == sum_recursive(i as nat) as u64,
    {
        let odd = 2 * i + 1;
        sum = sum + odd * odd * odd * odd;
        i = i + 1;
    }
    
    proof {
        sum_lemma(n);
        assert(sum == sum_recursive(n) as u64);
    }
    
    sum
}
// </vc-code>

}
fn main() {}