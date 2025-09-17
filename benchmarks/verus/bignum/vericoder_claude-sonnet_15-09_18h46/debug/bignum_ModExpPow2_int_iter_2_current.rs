use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
  decreases y 
{
  if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

// <vc-helpers>
spec fn mod_exp(base: nat, exp: nat, modulus: nat) -> nat
    decreases exp
{
    if modulus == 0 { 0 }
    else if exp == 0 { 1 % modulus }
    else if exp % 2 == 0 {
        let half_exp = mod_exp(base, exp / 2, modulus);
        (half_exp * half_exp) % modulus
    } else {
        (base * mod_exp(base, exp - 1, modulus)) % modulus
    }
}

proof fn exp_pow2_lemma(x: nat, n: nat)
    ensures Exp_int(x, Exp_int(2, n)) == if n == 0 { x } else { Exp_int(Exp_int(x, Exp_int(2, n - 1)), 2) }
{
    if n == 0 {
        assert(Exp_int(2, 0) == 1);
        assert(Exp_int(x, 1) == x);
    } else {
        assert(Exp_int(2, n) == 2 * Exp_int(2, n - 1));
    }
}

/* helper modified by LLM (iteration 2): added ghost function for safe nat conversion */
proof fn half_y_value(n: u64) -> (half_y: u64)
    requires n > 0
    ensures (half_y as nat) == Exp_int(2, (n - 1) as nat)
{
    proof {
        let target_exp = Exp_int(2, (n - 1) as nat);
        assert(target_exp < 18446744073709551616); // 2^64
    }
    target_exp as u64
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
    /* code modified by LLM (iteration 2): use ghost function for nat conversion */
    if n == 0u64 {
        assert(y == 1u64);
        if x == 0u64 {
            return 0u64;
        } else {
            return (x % z);
        }
    } else {
        proof {
            let ghost half_y_nat = Exp_int(2, (n - 1) as nat);
            assert(half_y_nat < 18446744073709551616);
        }
        let half_y = Exp_int(2, (n - 1) as nat) as u64;
        let half_res = ModExpPow2_int(x, half_y, n - 1, z);
        let result = ((half_res as u128 * half_res as u128) % z as u128) as u64;
        result
    }
}
// </vc-code>

fn main() {}
}


