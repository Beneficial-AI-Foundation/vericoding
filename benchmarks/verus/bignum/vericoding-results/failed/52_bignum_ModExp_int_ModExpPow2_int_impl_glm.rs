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
/* helper modified by LLM (iteration 4): fixed parsing error in assert statement */
fn compute_pow2_mod(x: u8, n: u8, z: u8) -> (res: u8)
    requires 
        (z as nat) > 1,
    ensures (res as nat) == exp_int(x as nat, exp_int(2, n as nat)) % (z as nat)
    decreases n
{
    if n == 0 {
        let res = x % z;
        proof {
            assert(exp_int(x as nat, exp_int(2, 0)) == exp_int(x as nat, 1));
            assert(exp_int(x as nat, 1) == x as nat);
            assert((res as nat) == (x as nat) % (z as nat));
        }
        res
    } else {
        let prev = compute_pow2_mod(x, n-1, z);
        let prev_u16 = prev as u16;
        let z_u16 = z as u16;
        let product = prev_u16 * prev_u16;
        let prev_sq = product % z_u16;
        let res = prev_sq as u8;
        proof {
            // Show that the multiplication doesn't overflow
            assert(prev_u16 as nat == prev as nat);
            assert(z_u16 as nat == z as nat);
            // Fix: break the assertion into two lines to avoid parsing error
            let p = prev as nat;
            let z_nat = z as nat;
            assert(p < z_nat);
            assert(prev as nat <= (z as nat - 1));
            assert(product as nat == (prev as nat) * (prev as nat));
            assert((prev as nat) * (prev as nat) <= (z as nat - 1) * (z as nat - 1));
            assert(254 * 254 == 64516);
            assert(64516 < 65536); // u16::MAX + 1

            // Show that the result satisfies the postcondition
            assert(prev_sq as nat == (product as nat) % (z as nat));
            assert(prev_sq as nat == ( (prev as nat) * (prev as nat) ) % (z as nat));
            // By the recursive call:
            assert(prev as nat == exp_int(x as nat, exp_int(2, (n-1) as nat)) % (z as nat));
            // Therefore:
            assert( (prev as nat) * (prev as nat) % (z as nat) 
                == ( (exp_int(x as nat, exp_int(2, (n-1) as nat)) % (z as nat)) * (exp_int(x as nat, exp_int(2, (n-1) as nat)) % (z as nat)) ) % (z as nat) );
            // By the property of modulus: (a % z) * (b % z) % z = (a * b) % z
            assert( ( (exp_int(x as nat, exp_int(2, (n-1) as nat)) % (z as nat)) * (exp_int(x as nat, exp_int(2, (n-1) as nat)) % (z as nat)) ) % (z as nat)
                == (exp_int(x as nat, exp_int(2, (n-1) as nat)) * exp_int(x as nat, exp_int(2, (n-1) as nat))) % (z as nat) );
            // And note: exp_int(x, exp_int(2, n)) = exp_int(x, exp_int(2, n-1) * 2) = exp_int(x, exp_int(2, n-1)) * exp_int(x, exp_int(2, n-1))
            assert(exp_int(x as nat, exp_int(2, n as nat)) == exp_int(x as nat, exp_int(2, (n-1) as nat)) * exp_int(x as nat, exp_int(2, (n-1) as nat)));
            // Therefore:
            assert(prev_sq as nat == exp_int(x as nat, exp_int(2, n as nat)) % (z as nat));
        }
        res
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
/* code modified by LLM (iteration 3): fixed syntax error in assert statement */
{
    if n == 0 {
        if y == 0 {
            1 % z
        } else {
            x % z
        }
    } else {
        let base = compute_pow2_mod(x, n, z);
        // Handle bit shifts safely for n>=8
        let (bit_set, y_low) = if n < 8 {
            ((y >> n) & 1 != 0, y & ((1 << n) - 1))
        } else {
            (false, y)
        };
        let part1 = if bit_set { base } else { 1 };
        let part2 = mod_exp_int(x, y_low, n-1, z);
        let result = (part1 as u16 * part2 as u16) % (z as u16);
        result as u8
    }
}
// </vc-code>


}

fn main() {}