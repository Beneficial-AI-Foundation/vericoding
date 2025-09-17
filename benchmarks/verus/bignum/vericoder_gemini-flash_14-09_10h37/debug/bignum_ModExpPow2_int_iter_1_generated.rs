use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
  decreases y 
{
  if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

// <vc-helpers>
spec fn Exp(x: nat, e: nat) -> nat decreases e { if e == 0 { 1 } else { x * Exp(x, (e - 1) as nat) } }
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
    if n == 0 {
        x % z
    } else {
        let res_prev = ModExpPow2_int(x, Exp(2, (n - 1) as nat) as u64, n - 1, z);
        let res = (res_prev as u128 * res_prev as u128) % (z as u128);
        res as u64
    }
}
// </vc-code>

fn main() {}
}


