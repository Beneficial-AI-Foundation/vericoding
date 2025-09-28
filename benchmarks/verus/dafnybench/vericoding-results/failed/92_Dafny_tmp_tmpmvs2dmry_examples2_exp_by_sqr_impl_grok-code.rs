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
spec fn pow(base: int, exp: nat) -> int
decreases exp
{
    if exp == 0 {
        1
    } else if base == 0 {
        0
    } else {
        base * pow(base, exp - 1)
    }
}

proof fn lemma_pow_equals_exp(x: int, n: nat)
ensures exp(x, n) == pow(x, n)
decreases n
{
    if n == 0 {
    } else if x == 0 {
    } else {
        lemma_pow_equals_exp(x, n - 1);
    }
}

proof fn lemma_exp_mul(x: int, n: nat, m: nat)
ensures exp(x, n) * exp(x, m) == exp(x, n + m)
decreases n
{
    if n == 0 {
        // exp(x, 0) * exp(x, m) == exp(x, m)
    } else if x == 0 {
        if n > 0 {
            assert(exp(x, n) == 0);
            // 0 * exp(x, m) == 0
            // exp(x, n+m) == 0
        }
    } else {
        assert(exp(x, n) == x * exp(x, n-1));
        lemma_exp_mul(x, n-1, m);
        assert(exp(x, n) * exp(x, m) == x * (exp(x, n-1) * exp(x, m)));
        assert(exp(x, n+m) == x * exp(x, n-1 + m));
    }
}

proof fn lemma_exp_step(x: int, n: nat)
ensures x * exp(x, n) == exp(x, n+1)
{
    if n == 0 {
        // exp(x, 1) == x
    } else if x == 0 {
        // x * exp(x, n) == 0
        // exp(x, n+1) == 0
    } else {
        // by definition
        assert(exp(x, n+1) == x * exp(x, n));
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
        1 as u32
    } else {
        let half = n0 / 2;
        let halfpow = exp_by_sqr(x0, half);
        let square: int = (halfpow as int) * (halfpow as int);
        proof {};
        with {
            assert(halfpow as int == exp(x0 as int, half as nat));
            lemma_exp_mul(x0 as int, half as nat, half as nat);
            assert(square == exp(x0 as int, (half as nat) + (half as nat)));
        };
        if n0 % 2 == 1 {
            assert(n0 % 2 == 1);
            assert(n0 == 2 * half + 1);
            let final = square * (x0 as int);
            proof {};
            with {
                lemma_exp_step(x0 as int, half as nat + half as nat);
                assert(final == exp(x0 as int, half as nat + half as nat + 1));
                assert(half as nat + half as nat + 1 == (2 * half + 1) == n0 as nat);
            };
            final as u32
        } else {
            proof {};
            with {
                assert(n0 % 2 == 0);
                assert(n0 == 2 * half);
                assert(2 * (half as nat) == n0 as nat);
                assert(square == exp(x0 as int, n0 as nat));
            };
            square as u32
        }
    }
}
// </vc-code>

fn main() {
}

}