// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn exp_int(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 { 1 } else { x * exp_int(x, (y - 1) as nat) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed type mismatch by ensuring consistent int types in spec functions */
proof fn base_case(x: u8, z: u8) -> (res: u8)
    requires z > 0
    ensures res as nat == exp_int(x as nat, 1) % (z as nat)
{
    let exp_result = (x as int) % (z as int);
    (exp_result as u8)
}

proof fn inductive_step(x: u8, power: u8, z: u8, n: u8) -> (res: u8)
    requires
        n > 0,
        z > 0,
        power as nat == exp_int(2, (n - 1) as nat)
    ensures
        res as nat == exp_int(x as nat, (2 * power) as nat) % (z as nat)
{
    let half_power_val = (exp_int(x as nat, power as nat) % (z as nat)) as int;
    let result_squared = (half_power_val * half_power_val) % (z as int);
    (result_squared as u8)
}
// </vc-helpers>

// <vc-spec>
fn mod_exp_pow2_int(x: u8, y: u8, n: u8, z: u8) -> (res: u8)
    requires 
        y as nat == exp_int(2, n as nat),
        z > 0,
    ensures res as nat == exp_int(x as nat, y as nat) % (z as nat)
    decreases n
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fixed type mismatch by using consistent int arithmetic throughout */
{
    if n == 0 {
        // Base case: x^1 % z
        ((x as int) % (z as int)) as u8
    } else {
        let half_n = n - 1;
        let half_power_val = (1u16 << half_n) as u8;
        let intermediate = mod_exp_pow2_int(x, half_power_val, half_n, z);
        let result_squared = (intermediate as int * intermediate as int) % (z as int);
        (result_squared as u8)
    }
}
// </vc-code>


}

fn main() {}