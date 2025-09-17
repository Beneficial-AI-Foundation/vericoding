use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
  decreases y 
{
  if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

// <vc-helpers>
spec fn mod_mul(a: nat, b: nat, m: nat) -> nat
{
  if m > 0 { (a * b) % m } else { 0 }
}

proof fn lemma_mod_mul_distributes(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
  // This is a standard property in number theory
  vstd::arithmetic::mod_::mod_mul_equal(a, b, m);
}

proof fn lemma_exp_base_cases(x: nat)
  requires true
  ensures Exp_int(x, 0) == 1
  ensures Exp_int(x, 1) == x
{
  // Base cases follow from definition
}

proof fn lemma_exp_unfold(x: nat, y: nat)
  requires y > 0
  ensures Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat)
{
  // Follows from definition
}

proof fn lemma_exp_double(x: nat, y: nat)
  ensures Exp_int(x, 2 * y) == Exp_int(Exp_int(x, y), 2)
  decreases y
{
  if y == 0 {
    lemma_exp_base_cases(x);
  } else {
    lemma_exp_double(x, (y - 1) as nat);
    lemma_exp_unfold(x, 2 * y);
    lemma_exp_unfold(x, 2 * ((y - 1) as nat) + 2);
    lemma_exp_unfold(x, 2 * ((y - 1) as nat) + 1);
    lemma_exp_unfold(x, 2 * ((y - 1) as nat));
    lemma_exp_unfold(Exp_int(x, y), 2);
    lemma_exp_unfold(x, y);
    lemma_exp_base_cases(Exp_int(x, y));
  }
}

proof fn lemma_exp_pow2_structure(x: nat, n: nat)
  ensures Exp_int(x, Exp_int(2, n)) == if n == 0 { x } else { Exp_int(Exp_int(x, Exp_int(2, (n - 1) as nat)), 2) }
  decreases n
{
  if n == 0 {
    lemma_exp_base_cases(2);
    lemma_exp_base_cases(x);
  } else {
    lemma_exp_unfold(2, n);
    lemma_exp_double(x, Exp_int(2, (n - 1) as nat));
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
    proof {
      lemma_exp_base_cases(2);
      lemma_exp_base_cases(x as nat);
    }
    return x % z;
  } else {
    let half_exp = ModExpPow2_int(x, y / 2u64, n - 1u64, z);
    let result = ((half_exp as u128) * (half_exp as u128) % (z as u128)) as u64;
    
    proof {
      assert(y == Exp_int(2, n as nat));
      assert(n > 0);
      lemma_exp_unfold(2, n as nat);
      assert(Exp_int(2, n as nat) == 2 * Exp_int(2, (n - 1) as nat));
      assert(y / 2u64 == Exp_int(2, (n - 1) as nat));
      
      lemma_exp_pow2_structure(x as nat, n as nat);
      assert(Exp_int(x as nat, y as nat) == Exp_int(Exp_int(x as nat, (y / 2u64) as nat), 2));
      
      lemma_exp_unfold(half_exp as nat, 2);
      assert(Exp_int(half_exp as nat, 2) == (half_exp as nat) * (half_exp as nat));
      
      lemma_mod_mul_distributes(half_exp as nat, half_exp as nat, z as nat);
      
      assert((half_exp as u128) * (half_exp as u128) < u128::MAX);
      assert(result as nat == ((half_exp as nat) * (half_exp as nat)) % (z as nat));
      assert(result as nat == Exp_int(half_exp as nat, 2) % (z as nat));
      assert(result as nat == Exp_int(Exp_int(x as nat, (y / 2u64) as nat), 2) % (z as nat));
      assert(result as nat == Exp_int(x as nat, y as nat) % (z as nat));
    }
    
    return result;
  }
}
// </vc-code>

fn main() {}
}