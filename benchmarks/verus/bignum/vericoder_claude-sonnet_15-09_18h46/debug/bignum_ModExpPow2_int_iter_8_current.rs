use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
  decreases y 
{
  if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

// <vc-helpers>
/* helper modified by LLM (iteration 8): fix lemma to prove properties step by step and remove unused mod_exp */
proof fn exp_pow2_lemma(x: nat, n: nat)
    ensures Exp_int(x, Exp_int(2, n)) == if n == 0 { x } else { Exp_int(Exp_int(x, Exp_int(2, (n - 1) as nat)), 2) }
{
    if n == 0 {
        assert(Exp_int(2, 0) == 1);
        assert(Exp_int(x, Exp_int(2, 0)) == Exp_int(x, 1));
        assert(Exp_int(x, 1) == x * Exp_int(x, 0));
        assert(Exp_int(x, 0) == 1);
        assert(x * 1 == x);
    } else {
        assert(Exp_int(2, n) == 2 * Exp_int(2, (n - 1) as nat));
        let half_exp = Exp_int(2, (n - 1) as nat);
        assert(Exp_int(x, Exp_int(2, n)) == Exp_int(x, 2 * half_exp));
        assert(Exp_int(x, 2 * half_exp) == Exp_int(Exp_int(x, half_exp), 2));
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
    /* code modified by LLM (iteration 8): fix overflow and add proper assertions for verification */
    if n == 0u64 {
        assert(y == 1u64);
        assert(Exp_int(x as nat, y as nat) == Exp_int(x as nat, 1));
        assert(Exp_int(x as nat, 1) == x as nat);
        return (x % z);
    } else {
        assert(y > 0);
        assert(y % 2 == 0);
        let half_y = y / 2u64;
        assert(half_y < y);
        let half_res = ModExpPow2_int(x, half_y, n - 1, z);
        assert(half_res < z);
        let temp = (half_res as u128 * half_res as u128);
        assert(temp < z as u128 * z as u128);
        let result = (temp % z as u128) as u64;
        assert(result < z);
        result
    }
}
// </vc-code>

fn main() {}
}


