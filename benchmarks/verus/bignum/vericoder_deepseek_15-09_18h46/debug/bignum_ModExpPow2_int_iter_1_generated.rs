use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
  decreases y 
{
  if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

// <vc-helpers>

proof fn lemma_pow_add(x: nat, y: nat, z: nat)
    ensures Exp_int(x, y + z) == Exp_int(x, y) * Exp_int(x, z)
    decreases y
{
    if y > 0 {
        lemma_pow_add(x, y - 1, z + 1);
        assert(Exp_int(x, y + z) == x * Exp_int(x, y - 1 + z)) by {}
        assert(Exp_int(x, y - 1 + z) == Exp_int(x, y - 1) * Exp_int(x, z)) by {}
    }
}

proof fn lemma_mod_mul_property(a: nat, b: nat, m: nat)
    requires m > 0
    ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

proof fn lemma_pow2_exp(n: nat)
    ensures Exp_int(2, n) == (1u64 << n) as nat
    decreases n
{
    if n > 0 {
        lemma_pow2_exp(n - 1);
        assert((1u64 << n) == 2 * (1u64 << (n - 1))) by { bit_shl_repr(n as u64); };
    }
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
    if n == 0 {
        assert(Exp_int(2, 0) == 1) by { compute; };
        assert(y == 1) by { lemma_pow2_exp(n as nat); };
        return x % z;
    }
    
    let half_n = n - 1;
    let half_y = y / 2;
    
    proof {
        lemma_pow2_exp(n as nat);
        lemma_pow2_exp((n - 1) as nat);
        assert(Exp_int(2, n as nat) == 2 * Exp_int(2, (n - 1) as nat)) by { lemma_pow_add(2, (n - 1) as nat, 1); };
        assert(y == 2 * half_y) by {};
    }
    
    let half_result = ModExpPow2_int(x, half_y, half_n, z);
    
    proof {
        lemma_mod_mul_property(half_result as nat, half_result as nat, z as nat);
    }
    
    let result = (half_result * half_result) % z;
    
    result
}
// </vc-code>

fn main() {}
}


