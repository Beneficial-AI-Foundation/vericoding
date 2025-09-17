use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
  decreases y 
{
  if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

// <vc-helpers>
spec fn mod_mul(a: nat, b: nat, m: nat) -> nat
  requires m > 0
{
  (a * b) % m
}

proof fn lemma_mod_mul_distributes(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

proof fn lemma_exp_double(x: nat, y: nat)
  ensures Exp_int(x, 2 * y) == Exp_int(Exp_int(x, y), 2)
  decreases y
{
  if y == 0 {
  } else {
    lemma_exp_double(x, y - 1);
    assert(Exp_int(x, 2 * y) == Exp_int(x, 2 * (y - 1) + 2));
    assert(Exp_int(x, 2 * (y - 1) + 2) == x * x * Exp_int(x, 2 * (y - 1)));
    assert(Exp_int(x, 2 * (y - 1)) == Exp_int(Exp_int(x, y - 1), 2));
    assert(Exp_int(Exp_int(x, y), 2) == Exp_int(x, y) * Exp_int(x, y));
    assert(Exp_int(x, y) == x * Exp_int(x, y - 1));
  }
}

proof fn lemma_exp_pow2_structure(x: nat, n: nat)
  ensures Exp_int(x, Exp_int(2, n)) == if n == 0 { x } else { Exp_int(Exp_int(x, Exp_int(2, n - 1)), 2) }
  decreases n
{
  if n == 0 {
    assert(Exp_int(2, 0) == 1);
    assert(Exp_int(x, 1) == x);
  } else {
    assert(Exp_int(2, n) == 2 * Exp_int(2, n - 1));
    lemma_exp_double(x, Exp_int(2, n - 1));
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
  if n == 0u64 {
    assert(Exp_int(2, 0) == 1);
    assert(y == 1u64);
    return x % z;
  } else {
    let half_exp = ModExpPow2_int(x, y / 2u64, n - 1u64, z);
    let result = ((half_exp as u128) * (half_exp as u128) % (z as u128)) as u64;
    
    proof {
      assert(y / 2u64 == Exp_int(2, (n - 1) as nat));
      lemma_exp_pow2_structure(x as nat, n as nat);
      assert(Exp_int(x as nat, y as nat) == Exp_int(Exp_int(x as nat, (y / 2u64) as nat), 2));
      assert(Exp_int(half_exp as nat, 2) == (half_exp as nat) * (half_exp as nat));
      lemma_mod_mul_distributes(half_exp as nat, half_exp as nat, z as nat);
    }
    
    return result;
  }
}
// </vc-code>

fn main() {}
}