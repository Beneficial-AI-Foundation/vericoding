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
/* helper modified by LLM (iteration 10): fixed invariant to match x instead of x_mod and added overflow bounds */
fn mod_exp_base(x: u8, y: u8, z: u8) -> (res: u8)
    requires
        (z as nat) > 1,
        (y as nat) <= 8,
        (z as nat) <= 15,
        (x as nat) < (z as nat),
    ensures (res as nat) == exp_int(x as nat, y as nat) % (z as nat)
{
    if y == 0 {
        1
    } else {
        let mut result = 1u8;
        let mut i = 0u8;
        let x_mod = x % z;
        
        while i < y
            invariant
                i <= y,
                (result as nat) == exp_int(x as nat, i as nat) % (z as nat),
                (z as nat) > 1,
                (z as nat) <= 15,
                (result as nat) < (z as nat),
                (x_mod as nat) < (z as nat),
                (result as u16) < 256,
                (x_mod as u16) < 256,
                (result as u16 * x_mod as u16) < 65536,
            decreases y - i
        {
            proof {
                assert((result as u16 * x_mod as u16) < 15 * 15);
                assert((result as u16 * x_mod as u16) < 256);
            }
            result = ((result as u16 * x_mod as u16) % (z as u16)) as u8;
            i = i + 1;
        }
        
        result
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
    /* code modified by LLM (iteration 10): added overflow bounds checking and proper casting assertions */
    if y == 0 {
        1
    } else if y == 1 {
        (x % z)
    } else if y <= 8 && z <= 15 && x < z {
        mod_exp_base(x, y, z)
    } else if y % 2 == 0 {
        let half_y = y / 2;
        if n > 0 {
            let half_exp = mod_exp_int(x, half_y, n - 1, z);
            proof {
                assert((half_exp as u16) < 256);
                assert((half_exp as u16) * (half_exp as u16) < 65536);
            }
            (((half_exp as u16) * (half_exp as u16)) % (z as u16)) as u8
        } else {
            1
        }
    } else {
        let half_y = y / 2;
        if n > 0 {
            let half_exp = mod_exp_int(x, half_y, n - 1, z);
            let x_mod = x % z;
            proof {
                assert((half_exp as u16) < 256);
                assert((half_exp as u16) * (half_exp as u16) < 65536);
                assert((x_mod as u16) < 256);
            }
            let temp1 = (((half_exp as u16) * (half_exp as u16)) % (z as u16)) as u8;
            proof {
                assert((temp1 as u16) < 256);
                assert((x_mod as u16) * (temp1 as u16) < 65536);
            }
            (((x_mod as u16) * (temp1 as u16)) % (z as u16)) as u8
        } else {
            1
        }
    }
}
// </vc-code>


}

fn main() {}