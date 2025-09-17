use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
  decreases y 
{
  if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

// <vc-helpers>
/* helper modified by LLM (iteration 2): named return as res to fix compilation error */
exec fn mod_exp_pow2(x: u64, n: u64, m: u64) -> (res: u64)
    requires
        m > 0u64,
    ensures
        (res as nat) == Exp_int(x as nat, Exp_int(2, n as nat)) % (m as nat),
    decreases n
{
    if n == 0 {
        x % m
    } else {
        let h = mod_exp_pow2(x, n - 1, m);
        ((h as u128 * h as u128) % (m as u128)) as u64
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
/* code modified by LLM (iteration 2): call helper and assign to res */
{
    let res = mod_exp_pow2(x, n, z);
    res
}
// </vc-code>

fn main() {}
}


