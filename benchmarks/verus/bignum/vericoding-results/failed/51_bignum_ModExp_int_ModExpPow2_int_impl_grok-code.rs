// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn exp_int(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 { 1 } else { x * exp_int(x, (y - 1) as nat) }
}

fn mod_exp_pow2_int(x: nat, y: nat, n: nat, z: nat) -> (res: nat)
    requires 
        y == exp_int(2, n),
        z > 0,
    ensures res == exp_int(x, y) % z
    decreases n
{
    assume(false);
    unreached()
}
// </vc-preamble>

// <vc-helpers>
spec fn spec_mod_exp_pow2_int(x: nat, y: nat, n: nat, z: nat) -> nat
    decreases n
{
    if n == 0 {
        x % z
    } else {
        let half = spec_mod_exp_pow2_int(x, (y / 2) as nat, (n - 1) as nat, z);
        (half * half) % z
    }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp_int(x: u8, y: u8, n: u8, z: u8) -> (res: u8)
    requires 
        (y as nat) < exp_int(2nat, (n as nat) + 1nat),
        (z as nat) > 1,
    ensures (res as nat) == exp_int(x as nat, y as nat) % (z as nat)
    decreases n
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 8): use nat for all calculations to prevent overflow */
    if n == 0 {
        if y == 0 {
            1
        } else {
            ((x as nat) % (z as nat)) as u8
        }
    } else {
        let half = (mod_exp_int(x, ((y as nat / 2) as u8), n - 1, z)) as nat;
        let half_sq = (half * half) % (z as nat);
        let result =
            if ((y as nat) % 2) == 0 {
                half_sq
            } else {
                (half_sq * (x as nat)) % (z as nat)
            };
        (result as u8)
    }
}
// </vc-code>


}

fn main() {}