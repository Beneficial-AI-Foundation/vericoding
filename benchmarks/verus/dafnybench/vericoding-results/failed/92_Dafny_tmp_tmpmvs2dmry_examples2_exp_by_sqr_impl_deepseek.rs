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
spec fn is_power_of_two(n: nat) -> bool {
    n > 0 && (n & (n - 1)) == 0
}

proof fn lemma_pow2_positive(n: nat)
    ensures
        exp(2, n) > 0,
{
    if n > 0 {
        lemma_pow2_positive((n - 1) as nat);
    }
}

proof fn lemma_pow2_sqr(n: nat)
    ensures
        exp(2, n) * exp(2, n) == exp(2, 2 * n),
{
    if n > 0 {
        lemma_pow2_sqr((n - 1) as nat);
    }
}

proof fn lemma_exp_properties(x: int, m: nat, n: nat)
    requires
        x != 0,
    ensures
        exp(x, m + n) == exp(x, m) * exp(x, n),
    decreases m,
{
    if m > 0 {
        lemma_exp_properties(x, (m - 1) as nat, n);
        assert(exp(x, m + n) == x * exp(x, (m - 1) + n));
        assert(exp(x, m) * exp(x, n) == x * exp(x, m - 1) * exp(x, n));
    }
}

proof fn lemma_exp_even_split(x: int, n: nat)
    requires
        x != 0,
        n > 0,
        n % 2 == 0,
    ensures
        exp(x, n) == exp(x * x, n / 2),
    decreases n,
{
    if n > 2 {
        lemma_exp_even_split(x, (n - 2) as nat);
        assert(exp(x, n - 2) == exp(x * x, (n - 2) / 2));
    }
    assert(exp(x, n) == (x * x) * exp(x, n - 2));
    assert(exp(x * x, n / 2) == (x * x) * exp(x * x, (n / 2) - 1));
    if n == 2 {
        assert(exp(x, 2) == x * x);
        assert(exp(x * x, 1) == x * x);
    }
}

proof fn lemma_exp_odd_split(x: int, n: nat)
    requires
        x != 0,
        n > 0,
        n % 2 == 1,
    ensures
        exp(x, n) == x * exp(x * x, n / 2),
    decreases n,
{
    if n > 1 {
        lemma_exp_even_split(x, (n - 1) as nat);
    }
    assert(exp(x, n) == x * exp(x, n - 1));
    if n > 1 {
        assert(exp(x, n - 1) == exp(x * x, (n - 1) / 2));
    }
    if n == 1 {
        assert(exp(x, 1) == x);
        assert(exp(x * x, 0) == 1);
    }
}

proof fn lemma_exp_zero_case(x: int, n: nat)
    ensures
        exp(x, n) == if n == 0 { 1 } else { x * exp(x, n - 1) },
{
}

proof fn lemma_exp_square_property(x: int, n: nat)
    requires
        x != 0,
        n > 0,
        n % 2 == 0,
    ensures
        exp(x, n) == exp(x * x, n / 2),
{
    lemma_exp_even_split(x, n);
}

proof fn lemma_exp_odd_property(x: int, n: nat)
    requires
        x != 0,
        n > 0,
        n % 2 == 1,
    ensures
        exp(x, n) == x * exp(x * x, n / 2),
{
    lemma_exp_odd_split(x, n);
}
// </vc-helpers>

// <vc-spec>
fn exp_by_sqr(x0: u32, n0: u32) -> (r: u32)
requires x0 >= 0;
ensures r == exp(x0 as int, n0 as nat);
// </vc-spec>
// <vc-code>
{
    let mut x = x0 as int;
    let mut n = n0 as nat;
    let mut r: int = 1;
    
    while n > 0
        invariant
            r * exp(x, n) == exp(x0 as int, n0 as nat),
        decreases n,
    {
        if n % 2 == 1 {
            proof {
                lemma_exp_odd_property(x, n);
            }
            r = r * x;
            n = (n - 1) as nat;
        }
        if n > 0 {
            proof {
                lemma_exp_square_property(x, n);
            }
            x = x * x;
            n = (n / 2) as nat;
        }
    }
    
    r as u32
}
// </vc-code>

fn main() {
}

}