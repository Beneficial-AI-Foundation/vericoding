use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
  decreases y 
{
  if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

// <vc-helpers>

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
  proof {
    assert(Exp_int(x as nat, y as nat) % (z as nat) < z as nat);
    assert((z as nat) <= (u64::MAX as nat));
  }
  (Exp_int(x as nat, y as nat) % (z as nat)) as u64
}
// </vc-code>

fn main() {}
}