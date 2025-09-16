use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
  decreases y 
{
  if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

// <vc-helpers>
fn mul_mod_u64(a: u64, b: u64, m: u64) -> (res: u64)
    requires
        m > 0u64,
    ensures
        (res as nat) == ((a as nat) * (b as nat)) % (m as nat),
        res < m,
{
    let prod: u128 = (a as u128) * (b as u128);
    let rem: u128 = prod % (m as u128);
    assert(rem < (m as u128));
    assert((m as u128) <= (u64::MAX as u128));
    let r: u64 = rem as u64;
    r
}

proof fn lemma_mod_mul_congruence(a: nat, b: nat, m: nat)
    requires
        m > 0,
    ensures
        ((a % m) * (b % m)) % m == (a * b) % m
{
}

proof fn lemma_exp_addition(a: nat, m: nat, n: nat)
    ensures
        Exp_int(a, m + n) == Exp_int(a, m) * Exp_int(a, n)
    decreases n
{
    if n == 0 {
    } else {
        lemma_exp_addition(a, m, (n - 1) as nat);
    }
}

proof fn lemma_pow2_step(k: nat)
    ensures
        Exp_int(2, k + 1) == Exp_int(2, k) + Exp_int(2, k)
    decreases k
{
}

proof fn lemma_exp_zero(a: nat)
    ensures
        Exp_int(a, 0) == 1
{
}

proof fn lemma_exp_one(a: nat)
    ensures
        Exp_int(a, 1) == a
{
}
// </vc-helpers>

// <vc-spec>
exec fn ModExpPow2_int(x: u64, y: u64, n: u64, z: u64) -> (res: u64)
  requires z > 0u64,
   (y as nat) == Exp_int(2, n as nat)
  ensures (res as nat) == Exp_int(x as nat, y as nat) % (z as nat)
  decreases n
// </vc-spec>
// <vc-code>
{
    let mut r: u64 = x % z;
    let mut k: u64 = 0u64;
    proof {
        lemma_exp_zero(2);
        lemma_exp_one(x as nat);
    }
    while k < n
        invariant
            z > 0u64,
            k <= n,
            (r as nat) == Exp_int(x as nat, Exp_int(2, k as nat)) % (z as nat),
        decreases n - k
    {
        let old_k: u64 = k;
        let old_r: u64 = r;
        r = mul_mod_u64(old_r, old_r, z);
        proof {
            lemma_mod_mul_congruence(Exp_int(x as nat, Exp_int(2, old_k as nat)), Exp_int(x as nat, Exp_int(2, old_k as nat)), z as nat);
            lemma_exp_addition(x as nat, Exp_int(2, old_k as nat), Exp_int(2, old_k as nat));
            lemma_pow2_step(old_k as nat);
        }
        k = k + 1u64;
    }
    r
}
// </vc-code>

fn main() {}
}


