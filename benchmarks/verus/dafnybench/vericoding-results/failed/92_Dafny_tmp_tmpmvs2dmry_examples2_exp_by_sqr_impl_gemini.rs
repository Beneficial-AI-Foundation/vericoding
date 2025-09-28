// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn gcd(m: nat, n: nat) -> nat
recommends m > 0 && n > 0
decreases m + n
{
    if m == n { 
        n 
    } else if m > n { 

        if m > n { gcd(1, n) } else { n }
    } else { 

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
// </vc-preamble>

// <vc-helpers>
proof fn lemma_exp_even(x: int, n: nat)
    requires n % 2 == 0
    ensures exp(x, n) == exp(x * x, n / 2)
    decreases n
{
    if n > 0 {
        lemma_exp_even(x, (n - 2) as nat);
    }
}

proof fn lemma_pow_is_le_exp(base: int, k: nat)
    requires
        base > 1,
        k >= 1,
    ensures base <= exp(base, k)
    decreases k
{
    if k > 1 {
        lemma_pow_is_le_exp(base, (k - 1) as nat);
    }
}
// </vc-helpers>

// <vc-spec>
fn exp_by_sqr(x0: u32, n0: u32) -> (r: u32)
    requires x0 >= 0
    ensures r == exp(x0 as int, n0 as nat)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Moved lemma call into a proof block to fix compilation error. */
    let mut r: u32 = 1;
    let mut x = x0;
    let mut n = n0;

    let ghost x0_int = x0 as int;
    let ghost n0_nat = n0 as nat;

    while n > 0
        invariant
            exp(x0_int, n0_nat) == (r as int) * exp(x as int, n as nat),
            exp(x0_int, n0_nat) <= u32::MAX,
        decreases n
    {
        if n % 2 == 1 {
            proof {
                if (x as int) > 1 && n > 1 {
                    lemma_pow_is_le_exp(x as int, (n-1) as nat);
                }
            }
            r = r * x;
            n = n - 1;
        } else {
            proof {
                lemma_exp_even(x as int, n as nat);
                if (x as int) > 1 {
                    let xx = (x as int) * (x as int);
                    if xx > 1 {
                        lemma_pow_is_le_exp(xx, (n/2) as nat);
                    }
                }
            }
            x = x * x;
            n = n / 2;
        }
    }
    r
}
// </vc-code>

}
fn main() {}