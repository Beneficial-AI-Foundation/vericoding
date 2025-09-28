// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn power(x: int, n: nat) -> int
    decreases n
{
    if n == 0 { 1 } else { x * power(x, (n - 1) as nat) }
}
// </vc-preamble>

// <vc-helpers>
proof fn power_add_lemma(x: int, a: nat, b: nat)
    ensures power(x, a + b) == power(x, a) * power(x, b)
    decreases a
{
    if a > 0 {
        power_add_lemma(x, (a - 1) as nat, b);
    }
}

/* helper modified by LLM (iteration 2): Added lemma for iterative squaring */
proof fn power_square_lemma(b: int, k: nat)
    ensures power(b, 2 * k) == power(b * b, k)
    decreases k
{
    if k > 0 {
        power_square_lemma(b, (k - 1) as nat);
    }
}
// </vc-helpers>

// <vc-spec>
fn power_dc(x: i64, n: u64) -> (p: i64)
    ensures p == power(x as int, n as nat)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): switched to iterative implementation to fix recursion error */
    if n == 0 {
        return 1;
    }

    let mut b: i64 = x;
    let mut e: u64 = n;
    let mut res: i64 = 1;

    while e > 0
        invariant
            e <= n,
            power(x as int, n as nat) == (res as int) * power(b as int, e as nat),
        decreases e
    {
        proof {
            let k = e / 2;
            if e % 2 == 0 {
                assert(e as nat == 2 * k as nat) by(nonlinear_arith);
            } else {
                assert(e as nat == 2 * k as nat + 1) by(nonlinear_arith);
            }
            power_square_lemma(b as int, k as nat);
        }

        if e % 2 == 1 {
            res = res * b;
        }
        b = b * b;
        e = e / 2;
    }
    res
}
// </vc-code>

}
fn main() {}