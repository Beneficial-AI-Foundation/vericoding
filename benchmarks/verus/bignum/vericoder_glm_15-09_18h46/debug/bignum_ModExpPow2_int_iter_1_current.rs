use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
  decreases y 
{
  if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

// <vc-helpers>
 proof fn Exp_int_lemma(x: nat, y: nat, k: nat)
    ensures Exp_int(x, y) * Exp_int(x, k) == Exp_int(x, y + k)
    decreases y
{
    if y == 0 {
        assert(1 * Exp_int(x, k) == Exp_int(x, k));
        assert(Exp_int(x, k) == Exp_int(x, 0 + k));
    } else {
        assert(Exp_int(x, y) * Exp_int(x, k) == x * Exp_int(x, y - 1) * Exp_int(x, k));
        Exp_int_lemma(x, (y - 1) as nat, k);
        assert(Exp_int(x, y - 1) * Exp_int(x, k) == Exp_int(x, y - 1 + k));
        assert(x * Exp_int(x, y - 1) * Exp_int(x, k) == x * Exp_int(x, y - 1 + k));
        assert(x * Exp_int(x, y - 1 + k) == Exp_int(x, y + k));
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
{
    if n == 0u64 {
        assert(y == 1u64);
        let result = x % z;
        assert((result as nat) == (x as nat) % (z as nat));
        assert((result as nat) == Exp_int(x as nat, 1u64 as nat) % (z as nat));
        assert((result as nat) == Exp_int(x as nat, y as nat) % (z as nat));
        result
    } else {
        let half_n = n - 1u64;
        let half_y = y / 2u64;
        assert(half_y as nat == Exp_int(2, half_n as nat));
        let half_exp = ModExpPow2_int(x, half_y, half_n, z);
        assert((half_exp as nat) == Exp_int(x as nat, half_y as nat) % (z as nat));
        let half_exp_dbl = (half_exp as u128 * half_exp as u128) % (z as u128);
        let mut result = half_exp_dbl as u64;
        assert((result as nat) == (half_exp * half_exp as nat) % (z as nat));
        assert((half_exp * half_exp as nat) % (z as nat) == (Exp_int(x as nat, half_y as nat) * Exp_int(x as nat, half_y as nat)) % (z as nat));
        assert((Exp_int(x as nat, half_y as nat) * Exp_int(x as nat, half_y as nat)) % (z as nat) == Exp_int(x as nat, half_y as nat + half_y as nat) % (z as nat));
        assert(Exp_int(x as nat, half_y as nat + half_y as nat) == Exp_int(x as nat, y as nat));
        assert((result as nat) == Exp_int(x as nat, y as nat) % (z as nat));
        result
    }
}
// </vc-code>

fn main() {}
}


