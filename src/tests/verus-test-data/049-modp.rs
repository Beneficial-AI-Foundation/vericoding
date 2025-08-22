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
// pure-end

fn modmul(a: u32, b: u32, p: u32) -> (mul: u32)
    by (nonlinear_arith)
    // pre-conditions-start
    requires
        p > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        mul == ((a as int) * (b as int)) % (p as int),
    // post-conditions-end
{
    // impl-start
    (((a as u64) * (b as u64)) % (p as u64)) as u32
    // impl-end
}

#[verifier::loop_isolation(false)]
fn modp(n: u32, p: u32) -> (r: u32)
    by (nonlinear_arith)
    // pre-conditions-start
    requires
        p > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        r == modp_rec(n as nat, p as nat),
    // post-conditions-end
{
    // impl-start
    let mut r = 1u32 % p;
    for i in 0..n
        // invariants-start
        invariant
            r == modp_rec(i as nat, p as nat),
        // invariants-end
    {
        r = modmul(r, 2, p);
    }
    r
    // impl-end
}

}
fn main() {}
