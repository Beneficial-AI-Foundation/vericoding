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
    let result = ((a as u64) * (b as u64)) % (p as u64);
    result as u32
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
    let mut result: u32 = 1 % p;
    let mut i: u32 = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while i < n
        invariant
            p > 0,
            i <= n,
            result == modp_rec(i as nat, p as nat),
        decreases n - i,
    {
        result = modmul(result, 2, p);
        i = i + 1;
    }
    
    result
}

}
fn main() {}