use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
  decreases y 
{
  if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

// <vc-helpers>
/* helper modified by LLM (iteration 9): Fix assertions and missing lemmas */
proof fn lemma_pow2_exp(n: nat)
    ensures Exp_int(2, n) == (1u64 << n) as nat
    decreases n
{
    if n == 0 {
        assert(Exp_int(2, 0) == 1);
        assert((1u64 << 0) == 1u64);
    } else {
        let sub_n: nat = (n - 1) as nat;
        lemma_pow2_exp(sub_n);
        assert(Exp_int(2, n) == 2 * Exp_int(2, sub_n));
        assert(Exp_int(2, sub_n) == (1u64 << sub_n) as nat);
        assert((1u64 << n) == (1u64 << sub_n) << 1);
        assert((1u64 << sub_n) << 1 == 2u64 * (1u64 << sub_n));
    }
}

proof fn lemma_mod_mul_property(a: nat, b: nat, m: nat)
    requires m > 0
    ensures (a * b) % m == (a % m) * (b % m) % m
{
    assert((a * b) % m == (a % m) * (b % m) % m) by {
        // Standard modular arithmetic property
        simplify;
    };
}

proof fn lemma_exp_int_base2_zero()
    ensures Exp_int(2, 0) == 1
{
}

proof fn lemma_exp_int_base2_recursive(n: nat)
    requires n > 0
    ensures Exp_int(2, n) == 2 * Exp_int(2, (n - 1) as nat)
{
}

proof fn lemma_bitshift_power_of_two(n: nat)
    requires n != 0
    ensures (1u64 << n) == 2u64 * (1u64 << (n - 1))
{
    if n > 0 {
        assert((1u64 << n) == (1u64 << (n - 1)) << 1);
        assert((1u64 << (n - 1)) << 1 == 2u64 * (1u64 << (n - 1)));
    }
}

proof fn lemma_u64_to_u128_mod(a: u64, m: u64)
    requires m > 0
    ensures (a as u128 % m as u128) as u64 == a % m
{
    assert(a as u128 % m as u128 == (a % m) as u128);
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
/* code modified by LLM (iteration 9): Fix base case, type conversions, and modular arithmetic */
{
    if n == 0 {
        proof { 
            lemma_exp_int_base2_zero();
            assert(Exp_int(2, 0) == 1);
            assert((y as nat) == 1);
            assert(Exp_int(x as nat, y as nat) == x as nat);
        }
        return x % z;
    }
    
    let half_n = (n - 1) as u64;
    let half_exp = ((1u64 << half_n) as u64);
    
    proof {
        let n_nat: nat = n as nat;
        lemma_pow2_exp(n_nat);
        assert((y as nat) == Exp_int(2, n_nat));
        assert(Exp_int(2, n_nat) == (1u64 << n) as nat);
        assert(Exp_int(2, n_nat) == 2 * Exp_int(2, (n_nat - 1) as nat));
        assert(Exp_int(2, (n_nat - 1) as nat) == (1u64 << half_n) as nat);
    }
    
    let half_result = ModExpPow2_int(x, half_exp, half_n, z);
    
    proof {
        lemma_mod_mul_property(half_result as nat, half_result as nat, z as nat);
        assert(Exp_int(x as nat, y as nat) == Exp_int(x as nat, 2 * half_exp as nat));
        assert(Exp_int(x as nat, 2 * half_exp as nat) == Exp_int(x as nat, half_exp as nat) * Exp_int(x as nat, half_exp as nat));
    }
    
    let half_result_u128 = half_result as u128;
    let z_u128 = z as u128;
    let product = half_result_u128 * half_result_u128;
    let mod_result = (product % z_u128) as u64;
    
    mod_result
}
// </vc-code>

fn main() {}
}


