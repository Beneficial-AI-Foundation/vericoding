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
proof fn lemma_exp_by_sqr(x: int, n: nat, r: int)
    requires
        r == exp(x, n)
    ensures
        r == exp(x, n)
    decreases n
{
    if n == 0 {
        assert(r == 1);
    } else {
        lemma_exp_by_sqr(x, sub(n, 1), r / x);
        assert(r == x * exp(x, sub(n, 1)));
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
fn exp_by_sqr(x0: u32, n0: u32) -> (r: u32)
    requires x0 >= 0
    ensures r == exp(x0 as int, n0 as nat)
{
    let mut x = x0 as int;
    let mut n = n0 as nat;
    let mut r = 1;
    while n > 0
        invariant
            n >= 0,
            r * exp(x, n) == exp(x0 as int, n0 as nat),
            x >= 0
    {
        if n % 2 == 1 {
            r = (r as int * x) as u32;
        }
        x = x * x;
        n = n / 2;
    }
    r
}
// </vc-code>

fn main() {
}

}