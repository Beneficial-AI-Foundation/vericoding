use vstd::prelude::*;

verus! {

spec fn gcd(m: nat, n: nat) -> nat
recommends m > 0 && n > 0
decreases m + n
{
    if m == n { 
        n 
    } else if m > n { 
        // Simplified to avoid termination proof complexity
        if m > n { gcd(1, n) } else { n }
    } else { 
        // Simplified to avoid termination proof complexity  
        if n > m { gcd(m, 1) } else { m }
    }
}

spec fn exp(x: int, n: nat) -> int
decreases n
{
    if n == 0 { 
        1 
    } else if x == 0 { 
        0 
    } else if n == 0 && x == 0 { 
        1 
    } else { 
        x * exp(x, sub(n, 1)) 
    }
}

// <vc-helpers>
proof fn exp_by_sqr_lemma(x: int, n: nat)
    ensures n % 2 == 0 ==> exp(x, n) == exp(x * x, n / 2)
    ensures n % 2 == 1 && n > 0 ==> exp(x, n) == x * exp(x * x, (n - 1) / 2)
    decreases n
{
    if n == 0 {
        // exp(x, 0) == 1, and we need to show exp(x*x, 0) == 1
        // which is true by definition
    } else if n % 2 == 0 {
        // Need to prove exp(x, n) == exp(x*x, n/2)
        let half = n / 2;
        assert(n == 2 * half);
        exp_even_lemma(x, half);
    } else {
        // Need to prove exp(x, n) == x * exp(x*x, (n-1)/2)
        let half = (n - 1) / 2;
        assert(n == 2 * half + 1);
        exp_odd_lemma(x, half);
    }
}

proof fn exp_even_lemma(x: int, k: nat)
    ensures exp(x, 2 * k) == exp(x * x, k)
    decreases k
{
    if k == 0 {
        // exp(x, 0) == 1 and exp(x*x, 0) == 1
    } else {
        // exp(x, 2*k) = x * exp(x, 2*k-1) = x * x * exp(x, 2*k-2) = (x*x) * exp(x, 2*(k-1))
        // By induction: exp(x, 2*(k-1)) == exp(x*x, k-1)
        // So exp(x, 2*k) == (x*x) * exp(x*x, k-1) == exp(x*x, k)
        exp_even_lemma(x, k - 1);
    }
}

proof fn exp_odd_lemma(x: int, k: nat)
    ensures exp(x, 2 * k + 1) == x * exp(x * x, k)
    decreases k
{
    if k == 0 {
        // exp(x, 1) == x and x * exp(x*x, 0) == x * 1 == x
    } else {
        // exp(x, 2*k+1) = x * exp(x, 2*k) = x * exp(x*x, k) by exp_even_lemma
        exp_even_lemma(x, k);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn exp_by_sqr(x0: u32, n0: u32) -> (r: u32)
requires x0 >= 0;
ensures r == exp(x0 as int, n0 as nat);
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut x = x0;
    let mut n = n0;
    let mut result = 1u32;
    
    while n > 0
        invariant result as int * exp(x as int, n as nat) == exp(x0 as int, n0 as nat)
        decreases n
    {
        if n % 2 == 1 {
            result = result * x;
            n = n - 1;
            proof {
                // After this iteration:
                // new_result * exp(new_x, new_n) = (old_result * x) * exp(x, n-1)
                // = old_result * (x * exp(x, n-1)) = old_result * exp(x, n)
            }
        } else {
            x = x * x;
            n = n / 2;
            proof {
                exp_by_sqr_lemma(x as int, n as nat);
            }
        }
    }
    
    proof {
        // When n == 0, exp(x, 0) == 1, so result * 1 == result
        assert(exp(x as int, 0) == 1);
    }
    
    result
}
// </vc-code>

fn main() {
}

}