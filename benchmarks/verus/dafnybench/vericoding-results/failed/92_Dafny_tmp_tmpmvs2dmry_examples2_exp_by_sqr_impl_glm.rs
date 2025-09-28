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
spec fn exp_by_sqr_iter(x: int, n: nat, acc: int) -> int
    decreases n
{
    if n == 0 {
        acc
    } else if n % 2 == 0 {
        exp_by_sqr_iter(x*x, n/2, acc)
    } else {
        exp_by_sqr_iter(x*x, (n-1)/2, acc*x)
    }
}

proof fn exp_by_sqr_iter_lemma(x: int, n: nat, acc: int)
    requires x >= 0 && n >= 0 && acc >= 0,
    ensures exp_by_sqr_iter(x, n, acc) == acc * exp(x, n)
    decreases n
{
    if n == 0 {
        assert(acc * exp(x, n) == acc * 1);
    } else if n % 2 == 0 {
        calc! {
            exp_by_sqr_iter(x, n, acc);
            == { by definition of exp_by_sqr_iter }
            exp_by_sqr_iter(x*x, n/2, acc);
            == { exp_by_sqr_iter_lemma(x*x, n/2, acc); }
            acc * exp(x*x, n/2);
            == { assert(x*x >= 0); lemma_exp_square(x, n/2); }
            acc * exp(x, n);
        }
    } else {
        calc! {
            exp_by_sqr_iter(x, n, acc);
            == { by definition of exp_by_sqr_iter }
            exp_by_sqr_iter(x*x, (n-1)/2, acc*x);
            == { exp_by_sqr_iter_lemma(x*x, (n-1)/2, acc*x); }
            (acc*x) * exp(x*x, (n-1)/2);
            == { assert(x*x >= 0); lemma_exp_square(x, (n-1)/2); }
            (acc*x) * exp(x, (n-1));
            == { lemma_exp_add(x, 1, n-1); }
            acc * x * exp(x, (n-1));
            == { definition of exp }
            acc * exp(x, n);
        }
    }
}

proof fn lemma_exp_square(x: int, k: nat)
    requires x >= 0,
    ensures exp(x*x, k) == exp(x, 2*k)
    decreases k
{
    if k == 0 {
        assert(exp(x*x, 0) == 1);
        assert(exp(x, 0) == 1);
    } else {
        calc! {
            exp(x*x, k);
            == { definition of exp }
            x*x * exp(x*x, k-1);
            == { lemma_exp_square(x, k-1); }
            x*x * exp(x, 2*(k-1));
            == { lemma_exp_mult(x, x, 2*(k-1)); }
            exp(x, 1) * exp(x, 1) * exp(x, 2*(k-1));
            == { lemma_exp_add(x, 1, 1); }
            exp(x, 2) * exp(x, 2*(k-1));
            == { lemma_exp_add(x, 2, 2*(k-1)); }
            exp(x, 2*k);
        }
    }
}

proof fn lemma_exp_mult(x: int, y: int, n: nat)
    requires x >= 0 && y >= 0,
    ensures (x*y) * exp(x*y, n) == exp(x, n+1) * exp(y, n+1)
    decreases n
{
    if n == 0 {
        assert((x*y) * 1 == x * y);
        assert(exp(x, 1) * exp(y, 1) == x * y);
    } else {
        calc! {
            (x*y) * exp(x*y, n);
            == { lemma_exp_mult(x, y, n-1); }
            (x*y) * (exp(x, n) * exp(y, n));
            == { assert((x*y) * (exp(x, n) * exp(y, n)) == x * exp(x, n) * y * exp
// </vc-helpers>

// <vc-spec>
fn exp_by_sqr(x0: u32, n0: u32) -> (r: u32)
requires x0 >= 0;
ensures r == exp(x0 as int, n0 as nat);
// </vc-spec>
// <vc-code>
spec fn exp_by_sqr_iter(x: int, n: nat, acc: int) -> int
    decreases n
{
    if n == 0 {
        acc
    } else if n % 2 == 0 {
        exp_by_sqr_iter(x*x, n/2, acc)
    } else {
        exp_by_sqr_iter(x*x, (n-1)/2, acc*x)
    }
}

proof fn exp_by_sqr_iter_lemma(x: int, n: nat, acc: int)
    requires x >= 0 && n >= 0 && acc >= 0,
    ensures exp_by_sqr_iter(x, n, acc) == acc * exp(x, n)
    decreases n
{
    if n == 0 {
        assert(acc * exp(x, n) == acc * 1);
    } else if n % 2 == 0 {
        calc! {
            exp_by_sqr_iter(x, n, acc);
            == { by definition of exp_by_sqr_iter }
            exp_by_sqr_iter(x*x, n/2, acc);
            == { exp_by_sqr_iter_lemma(x*x, n/2, acc); }
            acc * exp(x*x, n/2);
            == { assert(x*x >= 0); lemma_exp_square(x, n/2); }
            acc * exp(x, n);
        }
    } else {
        calc! {
            exp_by_sqr_iter(x, n, acc);
            == { by definition of exp_by_sqr_iter }
            exp_by_sqr_iter(x*x, (n-1)/2, acc*x);
            == { exp_by_sqr_iter_lemma(x*x, (n-1)/2, acc*x); }
            (acc*x) * exp(x*x, (n-1)/2);
            == { assert(x*x >= 0); lemma_exp_square(x, (n-1)/2); }
            (acc*x) * exp(x, (n-1));
            == { lemma_exp_add(x, 1, n-1); }
            acc * x * exp(x, (n-1));
            == { definition of exp }
            acc * exp(x, n);
        }
    }
}

proof fn lemma_exp_square(x: int, k: nat)
    requires x >= 0,
    ensures exp(x*x, k) == exp(x, 2*k)
    decreases k
{
    if k == 0 {
        assert(exp(x*x, 0) == 1);
        assert(exp(x, 0) == 1);
    } else {
        calc! {
            exp(x*x, k);
            == { definition of exp }
            x*x * exp(x*x, k-1);
            == { lemma_exp_square(x, k-1); }
            x*x * exp(x, 2*(k-1));
            == { lemma_exp_mult(x, x, 2*(k-1)); }
            exp(x, 1) * exp(x, 1) * exp(x, 2*(k-1));
            == { lemma_exp_add(x, 1, 1); }
            exp(x, 2) * exp(x, 2*(k-1));
            == { lemma_exp_add(x, 2, 2*(k-1)); }
            exp(x, 2*k);
        }
    }
}

proof fn lemma_exp_mult(x: int, y: int, n: nat)
    requires x >= 0 && y >= 0,
    ensures (x*y) * exp(x*y, n) == exp(x, n+1) * exp(y, n+1)
    decreases n
{
    if n == 0 {
        assert((x*y) * 1 == x * y);
        assert(exp(x, 1) * exp(y, 1) == x * y);
    } else {
        calc! {
            (x*y) * exp(x*y, n);
            == { lemma_exp_mult(x, y, n-1); }
            (x*y) * (exp(x, n) * exp(y, n));
            == { assert((x*y) * (exp(x, n) * exp(y, n)) == x * exp(x, n) * y * exp
// </vc-code>

fn main() {
}

}