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
/* helper modified by LLM (iteration 10): Remove mod_exp_iterative_lemma and replace with direct proof logic */
spec fn mod_exp_lemma(x: nat, y: nat, z: nat, bit: nat)
    requires
        z > 0,
        bit <= 8
    ensures 
        exp_int(x, y) % z == (exp_int(x, y % exp_int(2, bit)) * exp_int(exp_int(x, exp_int(2, bit)), y / exp_int(2, bit))) % z
    decreases bit
{
    if bit > 0 {
        mod_exp_lemma(x, y, z, bit - 1);
        assert(y / exp_int(2, bit) * exp_int(2, bit) + y % exp_int(2, bit) == y);
        assert(exp_int(x, y) == exp_int(x, y % exp_int(2, bit)) * exp_int(exp_int(x, exp_int(2, bit)), y / exp_int(2, bit)));
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
    /* code modified by LLM (iteration 10): Use spec/proof functions properly and avoid calling nat functions in exec mode */
    if n == 0 {
        if y == 0 {
            return 1 % z;
        } else {
            return (x as u16 % z as u16) as u8;
        }
    } else {
        let prev = mod_exp_int(x, y, n - 1, z);
        proof {
            mod_exp_lemma(x as nat, y as nat, z as nat, n as nat);
        }
        
        let base = mod_exp_int(x, (1 << n) as u8, n, z);
        
        if y >= (1 << n) {
            let remainder = mod_exp_int(x, y - (1 << n), n - 1, z);
            (((base as u16 * remainder as u16) % z as u16) as u8)
        } else {
            prev
        }
    }
}
// </vc-code>


}

fn main() {}