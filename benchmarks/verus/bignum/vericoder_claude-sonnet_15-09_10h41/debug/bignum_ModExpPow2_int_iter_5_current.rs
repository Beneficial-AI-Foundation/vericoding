use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
  decreases y 
{
  if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

// <vc-helpers>
/* helper modified by LLM (iteration 5): added decreases clause to recursive proof function */
spec fn pow_mod(base: nat, exp: nat, modulus: nat) -> nat
{
    Exp_int(base, exp) % modulus
}

proof fn lemma_exp_double(x: nat, n: nat)
    ensures Exp_int(x, 2 * n) == Exp_int(Exp_int(x, n), 2)
    decreases n
{
    if n == 0 {
    } else {
        lemma_exp_double(x, (n - 1) as nat);
    }
}

proof fn lemma_mod_mul(a: nat, b: nat, m: nat)
    requires m > 0
    ensures (a * b) % m == ((a % m) * (b % m)) % m
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
/* code modified by LLM (iteration 5): fixed recursive call to use proper casting for nat type */
{
    if n == 0 {
        return 1u64;
    } else {
        let half_exp = ModExpPow2_int(x, y / 2, n - 1, z);
        let result = ((half_exp as u128) * (half_exp as u128)) % (z as u128);
        return result as u64;
    }
}
// </vc-code>

fn main() {}
}


