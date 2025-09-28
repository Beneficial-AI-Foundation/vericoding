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
/* helper modified by LLM (iteration 10): fixed bounds proof to handle all cases and added comprehensive precondition checking */
proof fn prove_bounds(y: u8, n: u8)
    requires 
        (y as nat) < exp_int(2nat, (n as nat) + 1nat),
        n > 0,
        y > 0
    ensures 
        y / 2 < 255,
        ((y / 2) as nat) < exp_int(2nat, ((n - 1) as nat) + 1nat),
        ((y - 1) as nat) < exp_int(2nat, (n as nat) + 1nat),
        n - 1 < 255
{
    assert(exp_int(2nat, (n as nat) + 1nat) == 2 * exp_int(2nat, n as nat));
    assert(exp_int(2nat, n as nat) == exp_int(2nat, ((n - 1) as nat) + 1nat));
    assert(y > 0);
    assert(((y / 2) as nat) <= ((y - 1) as nat));
    assert(((y - 1) as nat) < (y as nat));
    assert((y as nat) < exp_int(2nat, (n as nat) + 1nat));
    assert(y / 2 < y);
    assert(y / 2 < 255);
    assert(n - 1 < n);
    assert(n - 1 < 255);
}

proof fn prove_mult_bounds(temp: u8, z: u8)
    requires z >= 2
    ensures 
        temp < 255,
        (temp as u16) * (temp as u16) < 65536,
        ((temp as u16) * (temp as u16) % (z as u16)) as int < 256
{
    assert(temp < z);
    assert(z >= 2);
    assert(temp < 255);
    assert((temp as u16) < 256);
    assert((temp as u16) * (temp as u16) < 256 * 256);
    assert(256 * 256 == 65536);
    assert((temp as u16) * (temp as u16) % (z as u16) < (z as u16));
    assert((z as u16) <= 255);
    assert(((temp as u16) * (temp as u16) % (z as u16)) as int < 256);
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
    /* code modified by LLM (iteration 10): fixed type casting for modulo operation */
    if y == 0 {
        1 % z
    } else if n == 0 {
        if y == 1 {
            x % z
        } else {
            1 % z
        }
    } else if y % 2 == 0 {
        let half_y = y / 2;
        proof {
            prove_bounds(y, n);
        }
        let temp = mod_exp_int(x, half_y, n - 1, z);
        proof {
            prove_mult_bounds(temp, z);
        }
        let temp_wide: u16 = (temp as u16) * (temp as u16);
        ((temp_wide % (z as u16)) as int % (z as int)) as u8
    } else {
        proof {
            prove_bounds(y, n);
        }
        let temp = mod_exp_int(x, y - 1, n - 1, z);
        let result_wide: u16 = (x as u16) * (temp as u16);
        ((result_wide % (z as u16)) as int % (z as int)) as u8
    }
}
// </vc-code>


}

fn main() {}