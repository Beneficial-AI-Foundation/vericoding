// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn power(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 { 1 } else { x * power(x, (y - 1) as nat) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified helper to check if a number is a power */
fn compute_power(x: u64, y: u64) -> u64
{
    if y == 0 {
        1
    } else {
        let mut res: u64 = 1;
        let mut i: u64 = 0;
        
        while i < y
            invariant
                i <= y,
                res == power(x as nat, i as nat) as u64
            decreases y - i
        {
            res = res * x;
            i = i + 1;
        }
        res
    }
}
// </vc-helpers>

// <vc-spec>
fn is_simple_power(x: u8, n: i8) -> (ans: bool)
    requires x > 0
    ensures ans <==> exists|y: nat| n as int == power(x as nat, y) as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use helper function and simplified loop */
    if n < 0 {
        false
    } else {
        let mut y: u64 = 0;
        let n_u64 = n as u64;
        let x_u64 = x as u64;
        let mut found = false;
        
        while y <= 255
            invariant
                y <= 256,
                forall|z: u64| z < y ==> compute_power(x_u64, z) != n_u64,
                found == (exists|z: u64| z < y && compute_power(x_u64, z) == n_u64)
            decreases (256 - y)
        {
            let pow_val = compute_power(x_u64, y);
            
            if pow_val == n_u64 {
                found = true;
                break;
            } else if pow_val > n_u64 {
                break;
            }
            y = y + 1;
        }
        found
    }
}
// </vc-code>


}

fn main() {}