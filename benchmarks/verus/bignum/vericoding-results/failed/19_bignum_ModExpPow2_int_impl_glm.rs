use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
  decreases y 
{
  if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed associativity in Exp_int_lemma */
proof fn Exp_int_lemma(x: nat, y: nat, k: nat)
    ensures Exp_int(x, y) * Exp_int(x, k) == Exp_int(x, y + k)
    decreases y
{
    if y == 0 {
        assert(Exp_int(x,0) * Exp_int(x,k) == 1 * Exp_int(x,k));
        assert(1 * Exp_int(x,k) == Exp_int(x,k));
        assert(Exp_int(x,k) == Exp_int(x,0+k));
    } else {
        let y_minus_1 = (y - 1) as nat;
        Exp_int_lemma(x, y_minus_1, k);
        assert(Exp_int(x, y_minus_1) * Exp_int(x, k) == Exp_int(x, y_minus_1 + k));
        let a = Exp_int(x, y_minus_1);
        let b = Exp_int(x, k);
        let c = Exp_int(x, y_minus_1 + k);
        assert(a * b == c);
        let lhs = Exp_int(x, y) * Exp_int(x, k);
        let rhs = Exp_int(x, y + k);
        assert(lhs == (x * a) * b);
        assert((x * a) * b == x * (a * b));
        assert(x * (a * b) == x * c);
        assert(x * c == rhs);
        assert(lhs == rhs);
    }
}

pub closed spec fn Exp_int_mod(x: nat, y: nat, m: nat) -> nat
    recommends m > 0
{
    Exp_int(x, y) % m
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
/* code modified by LLM (iteration 3): fixed modulus and overflow issues */
{
    if n == 0u64 {
        assert(y == 1u64);
        let result = x % z;
        let x_nat = x as nat;
        let z_nat = z as nat;
        assert((x % z) as nat == x_nat % z_nat);
        assert(x_nat % z_nat == Exp_int(x_nat, 1) % z_nat);
        assert((result as nat) == Exp_int(x_nat, 1) % z_nat);
        assert(Exp_int(x_nat, 1) % z_nat == Exp_int(x_nat, y as nat) % z_nat);
        result
    } else {
        let half_n = n - 1u64;
        let half_y = y / 2u64;
        assert(half_y as nat == Exp_int(2, half_n as nat));
        let half_exp = ModExpPow2_int(x, half_y, half_n, z);
        assert((half_exp as nat) == Exp_int(x as nat, half_y as nat) % (z as nat));
        let a = half_exp as u128;
        let b = half_exp as u128;
        let z_128 = z as u128;
        let product = a * b;
        let half_exp_dbl = product % z_128;
        let mut result = half_exp_dbl as u64;
        let half_exp_nat = half_exp as nat;
        let z_nat = z as nat;
        let product_nat = half_exp_nat * half_exp_nat;
        assert(product == product_nat);
        let modulus_nat = product_nat % z_nat;
        let modulus_u128 = product % z_128;
        assert(modulus_u128 as nat == modulus_nat);
        assert(result as nat == modulus_nat);
        let a_exp = Exp_int(x as nat, half_y as nat);
        let a_mod = a_exp % z_nat;
        assert(a_mod == half_exp_nat);
        assert((a_mod * a_mod) % z_nat == (a_exp * a_exp) % z_nat);
        assert((a_exp * a_exp) % z_nat == Exp_int(x as nat, half_y as nat + half_y as nat) % z_nat);
        assert(Exp_int(x as nat, half_y as nat + half_y as nat) == Exp_int(x as nat, y as nat));
        assert((a_exp * a_exp) % z_nat == Exp_int(x as nat, y as nat) % z_nat);
        assert(modulus_nat == Exp_int(x as nat, y as nat) % z_nat);
        assert((result as nat) == Exp_int(x as nat, y as nat) % (z as nat));
        result
    }
}
// </vc-code>

fn main() {}
}


