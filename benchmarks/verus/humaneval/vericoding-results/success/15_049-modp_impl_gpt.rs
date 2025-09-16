// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn modp_rec(n: nat, p: nat) -> (result:nat)
    decreases n,
{
    if n == 0 {
        1nat % p
    } else {
        (modp_rec((n - 1) as nat, p) * 2) % p
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_modp_rec_step(i: nat, p: nat)
    ensures
        modp_rec(i + 1, p) == (modp_rec(i, p) * 2) % p,
{
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn modp(n: u32, p: u32) -> (r: u32)
    by (nonlinear_arith)

    requires
        p > 0,

    ensures
        r == modp_rec(n as nat, p as nat),
// </vc-spec>
// <vc-code>
{
    let mut i: u32 = 0u32;
    let mut acc: u32 = 1u32 % p;
    while i < n
        invariant
            p > 0,
            i <= n,
            acc == modp_rec(i as nat, p as nat),
        decreases (n - i) as nat
    {
        let prev_i: u32 = i;
        let prev_acc: u32 = acc;
        let tmp64: u64 = ((prev_acc as u64) * 2u64) % (p as u64);
        assert(tmp64 < p as u64);
        assert(p as u64 <= u32::MAX as u64);
        assert(tmp64 <= u32::MAX as u64);
        acc = tmp64 as u32;
        i = prev_i + 1;
        proof {
            lemma_modp_rec_step(prev_i as nat, p as nat);
        }
    }
    acc
}
// </vc-code>

}
fn main() {}