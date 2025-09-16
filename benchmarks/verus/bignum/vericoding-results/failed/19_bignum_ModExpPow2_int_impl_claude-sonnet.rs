use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
  decreases y 
{
  if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

// <vc-helpers>
/* helper modified by LLM (iteration 10): fix type error in exp_double_lemma recursive call */
proof fn exp_double_lemma(x: nat, k: nat)
    ensures Exp_int(x, 2 * k) == Exp_int(Exp_int(x, k), 2)
{
    if k == 0 {
        assert(Exp_int(x, 0) == 1);
        assert(Exp_int(1, 2) == 1);
        assert(Exp_int(x, 2 * 0) == Exp_int(x, 0));
    } else {
        exp_double_lemma(x, (k - 1) as nat);
    }
}

proof fn exp_one_lemma(x: nat)
    ensures Exp_int(x, 1) == x
{
    assert(Exp_int(x, 1) == x * Exp_int(x, 0));
    assert(Exp_int(x, 0) == 1);
}

proof fn exp_pow2_lemma(x: nat, n: nat)
    ensures Exp_int(x, Exp_int(2, n)) == if n == 0 { x } else { Exp_int(Exp_int(x, Exp_int(2, (n - 1) as nat)), 2) }
{
    if n == 0 {
        assert(Exp_int(2, 0) == 1);
        exp_one_lemma(x);
    } else {
        assert(Exp_int(2, n) == 2 * Exp_int(2, (n - 1) as nat));
        let half_exp = Exp_int(2, (n - 1) as nat);
        exp_double_lemma(x, half_exp);
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
    /* code modified by LLM (iteration 10): fix type error in exp_double_lemma recursive call */
    if n == 0u64 {
        proof {
            exp_pow2_lemma(x as nat, 0);
            exp_one_lemma(x as nat);
        }
        return (x % z);
    } else {
        let half_y = y / 2u64;
        let half_res = ModExpPow2_int(x, half_y, n - 1, z);
        
        proof {
            exp_pow2_lemma(x as nat, n as nat);
            exp_double_lemma(x as nat, half_y as nat);
            assert(y > 0u64);
        }
        
        if half_res <= 46340u64 {
            let temp = half_res * half_res;
            (temp % z)
        } else {
            let temp = (half_res as u128 * half_res as u128);
            (temp % z as u128) as u64
        }
    }
}
// </vc-code>

fn main() {}
}


