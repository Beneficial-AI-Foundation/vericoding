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
requires n > 0
ensures exp(x, n) == if n % 2 == 0 { exp(x * x, n / 2) } else { x * exp(x, n - 1) }
decreases n
{
    if n % 2 == 0 {
        let half_n = n / 2;
        assert(n == 2 * half_n);
        exp_even_lemma(x, n);
    } else {
        assert(n >= 1);
        assert(exp(x, n) == x * exp(x, n - 1));
    }
}

proof fn exp_even_lemma(x: int, n: nat)
requires n > 0 && n % 2 == 0
ensures exp(x, n) == exp(x * x, n / 2)
decreases n
{
    let half_n = n / 2;
    assert(n == 2 * half_n);
    exp_square_lemma(x, half_n);
}

proof fn exp_square_lemma(x: int, k: nat)
ensures exp(x, 2 * k) == exp(x * x, k)
decreases k
{
    if k == 0 {
        assert(exp(x, 0) == 1);
        assert(exp(x * x, 0) == 1);
    } else {
        assert(2 * k >= 2);
        assert(exp(x, 2 * k) == x * exp(x, 2 * k - 1));
        assert(exp(x, 2 * k - 1) == x * exp(x, 2 * k - 2));
        assert(exp(x, 2 * k) == x * x * exp(x, 2 * k - 2));
        assert(2 * k - 2 == 2 * (k - 1));
        exp_square_lemma(x, k - 1);
        assert(exp(x, 2 * (k - 1)) == exp(x * x, k - 1));
        assert(exp(x * x, k) == (x * x) * exp(x * x, k - 1));
    }
}

proof fn exp_positive_base(x: int, n: nat)
requires x > 0
ensures exp(x, n) > 0
decreases n
{
    if n == 0 {
        assert(exp(x, 0) == 1);
    } else {
        exp_positive_base(x, n - 1);
        assert(exp(x, n) == x * exp(x, n - 1));
    }
}

proof fn exp_base_zero(n: nat)
ensures exp(0, n) == if n == 0 { 1 } else { 0 }
{
    if n == 0 {
        assert(exp(0, 0) == 1);
    } else {
        assert(exp(0, n) == 0);
    }
}

proof fn exp_mult_lemma(x: int, a: nat, b: nat)
ensures exp(x, a) * exp(x, b) == exp(x, a + b)
decreases a
{
    if a == 0 {
        assert(exp(x, 0) == 1);
        assert(1 * exp(x, b) == exp(x, b));
        assert(0 + b == b);
    } else {
        exp_mult_lemma(x, a - 1, b);
        assert(exp(x, a) == x * exp(x, a - 1));
        assert(exp(x, a) * exp(x, b) == x * exp(x, a - 1) * exp(x, b));
        assert(exp(x, a - 1) * exp(x, b) == exp(x, (a - 1) + b));
        assert((a - 1) + b == a + b - 1);
        assert(exp(x, a + b) == x * exp(x, a + b - 1));
    }
}
// </vc-helpers>

// <vc-spec>
fn exp_by_sqr(x0: u32, n0: u32) -> (r: u32)
requires x0 >= 0;
ensures r == exp(x0 as int, n0 as nat);
// </vc-spec>
// <vc-code>
{
    if n0 == 0 {
        return 1u32;
    }
    
    let mut x = x0;
    let mut n = n0;
    let mut result = 1u32;
    
    while n > 0
        invariant 
            result as int * exp(x as int, n as nat) == exp(x0 as int, n0 as nat),
            result >= 1,
        decreases n
    {
        if n % 2 == 1 {
            proof {
                assert(n >= 1);
                exp_by_sqr_lemma(x as int, n as nat);
                assert(exp(x as int, n as nat) == (x as int) * exp(x as int, (n - 1) as nat));
            }
            result = result * x;
            n = n - 1;
            proof {
                assert((result as int) * exp(x as int, n as nat) == exp(x0 as int, n0 as nat));
            }
        } else {
            proof {
                assert(n > 0 && n % 2 == 0);
                exp_by_sqr_lemma(x as int, n as nat);
                assert(exp(x as int, n as nat) == exp((x * x) as int, (n / 2) as nat));
            }
            x = x * x;
            n = n / 2;
            proof {
                assert((result as int) * exp(x as int, n as nat) == exp(x0 as int, n0 as nat));
            }
        }
    }
    
    proof {
        assert(n == 0);
        assert(exp(x as int, 0) == 1);
        assert(result as int * 1 == exp(x0 as int, n0 as nat));
        assert(result as int == exp(x0 as int, n0 as nat));
    }
    
    result
}
// </vc-code>

fn main() {
}

}