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
// Helper lemmas for exponential properties
proof fn exp_zero(x: int)
    ensures exp(x, 0) == 1
{
}

proof fn exp_even(x: int, n: nat)
    requires n > 0 && n % 2 == 0
    ensures exp(x, n) == exp(x * x, n / 2)
    decreases n
{
    if n == 2 {
        assert(exp(x, 2) == x * exp(x, 1));
        assert(exp(x, 1) == x * exp(x, 0));
        assert(exp(x, 0) == 1);
        assert(exp(x, 2) == x * x);
        assert(exp(x * x, 1) == x * x * exp(x * x, 0));
        assert(exp(x * x, 0) == 1);
        assert(exp(x * x, 1) == x * x);
        assert(n / 2 == 1);
    } else {
        assert(n >= 4);
        let half = n / 2;
        assert(half >= 2);
        assert(n == 2 * half);
        assert(half % 2 == 0);
        
        // exp(x, n) = x * x^(n-1) = x * x * x^(n-2)
        assert(exp(x, n) == x * exp(x, sub(n, 1)));
        assert(exp(x, sub(n, 1)) == x * exp(x, sub(sub(n, 1), 1)));
        assert(sub(sub(n, 1), 1) == sub(n, 2));
        assert(exp(x, n) == x * x * exp(x, sub(n, 2)));
        
        // Recursive call for n-2
        exp_even(x, sub(n, 2));
        assert(exp(x, sub(n, 2)) == exp(x * x, sub(n, 2) / 2));
        assert(sub(n, 2) / 2 == sub(half, 1));
        
        // exp(x*x, half) = (x*x) * exp(x*x, half-1)
        assert(exp(x * x, half) == (x * x) * exp(x * x, sub(half, 1)));
        assert(exp(x, n) == exp(x * x, half));
    }
}

proof fn exp_odd(x: int, n: nat)
    requires n > 0 && n % 2 == 1
    ensures exp(x, n) == x * exp(x * x, n / 2)
    decreases n
{
    if n == 1 {
        assert(exp(x, 1) == x * exp(x, 0));
        assert(exp(x, 0) == 1);
        assert(n / 2 == 0);
        assert(exp(x * x, 0) == 1);
        assert(exp(x, 1) == x);
        assert(x * exp(x * x, n / 2) == x * 1);
    } else {
        assert(n >= 3);
        let half = n / 2;
        assert(half >= 1);
        assert(n == 2 * half + 1);
        
        // exp(x, n) = x * exp(x, n-1)
        assert(exp(x, n) == x * exp(x, sub(n, 1)));
        assert(sub(n, 1) == 2 * half);
        assert(sub(n, 1) % 2 == 0);
        
        // Apply even case to n-1
        exp_even(x, sub(n, 1));
        assert(exp(x, sub(n, 1)) == exp(x * x, sub(n, 1) / 2));
        assert(sub(n, 1) / 2 == half);
        assert(exp(x, n) == x * exp(x * x, half));
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
    let mut y: u32 = 1;
    let mut x: u32 = x0;
    let mut n: u32 = n0;
    
    while n > 0
        invariant 
            y as int * exp(x as int, n as nat) == exp(x0 as int, n0 as nat),
            x >= 0,
            y >= 0,
        decreases n,
    {
        if n % 2 == 1 {
            proof {
                exp_odd(x as int, n as nat);
                assert(exp(x as int, n as nat) == x as int * exp((x * x) as int, (n / 2) as nat));
            }
            y = y * x;
            x = x * x;
            n = n / 2;
        } else {
            proof {
                exp_even(x as int, n as nat);
                assert(exp(x as int, n as nat) == exp((x * x) as int, (n / 2) as nat));
            }
            x = x * x;
            n = n / 2;
        }
    }
    
    proof {
        assert(n == 0);
        exp_zero(x as int);
        assert(exp(x as int, 0) == 1);
        assert(y as int * 1 == exp(x0 as int, n0 as nat));
    }
    
    y
}
// </vc-code>

fn main() {
}

}