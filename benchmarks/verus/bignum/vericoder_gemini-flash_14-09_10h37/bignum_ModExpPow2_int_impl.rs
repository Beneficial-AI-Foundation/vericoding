use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
  decreases y 
{
  if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed helper since it's not needed by fixed code */
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
    /* code modified by LLM (iteration 5): fixed 'nat' to 'u64' casting for `n - 1` and adjusted the base case and recursive step calculation for ModExpPow2_int */
    if n == 0 {
        proof {
            assert((y as nat) == Exp_int(2, 0 as nat)); // y is 2^0 = 1
        }
        x % z
    } else {
        let y_prev_n = (n - 1);
        let res_prev = ModExpPow2_int(x, Exp_int(2, y_prev_n as nat) as u64, y_prev_n, z);
        let res = (res_prev as u128 * res_prev as u128) % (z as u128);
        res as u64
    }
}
// </vc-code>

fn main() {}
}


