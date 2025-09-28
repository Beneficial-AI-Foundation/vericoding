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
/* helper modified by LLM (iteration 10): Added lemmas for exp_int properties and modulo bounds */
proof fn lemma_exp_2_1()
    ensures exp_int(2nat, 1nat) == 2nat
{
    // By definition: exp_int(2, 1) = 2 * exp_int(2, 0) = 2 * 1 = 2
    assert(exp_int(2nat, 1nat) == 2nat * exp_int(2nat, 0nat));
    assert(exp_int(2nat, 0nat) == 1nat);
    assert(2nat * 1nat == 2nat);
}

proof fn lemma_mod_bound(a: nat, b: nat)
    requires b > 0
    ensures a % b < b
{
    // This is a basic property of modulo - Verus should know this
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
    /* code modified by LLM (iteration 10): Fixed bounds proof for half_result multiplication */
    if y == 0 {
        1u8
    } else if y == 1 {
        (x % z) as u8
    } else if n == 0 {
        // When n == 0, y < 2^1 = 2, so y can only be 0 or 1
        // Both cases are already handled above
        proof {
            lemma_exp_2_1();
            assert((y as nat) < exp_int(2nat, 1nat));
            assert(exp_int(2nat, 1nat) == 2nat);
            assert((y as nat) < 2nat);
            assert(y == 0 || y == 1);
            assert(false);  // This proves unreachability
        }
        unreached()
    } else if y % 2 == 0 {
        // y is even, so y = 2 * (y/2)
        let half_y = y / 2;
        proof {
            assert(n >= 1);
            assert((half_y as nat) < exp_int(2nat, n as nat));
        }
        let half_result = mod_exp_int(x, half_y, (n - 1) as u8, z);
        // half_result == exp_int(x, half_y) % z < z (by postcondition and modulo property)
        proof {
            assert((half_result as nat) == exp_int(x as nat, half_y as nat) % (z as nat));
            lemma_mod_bound(exp_int(x as nat, half_y as nat), z as nat);
            assert(exp_int(x as nat, half_y as nat) % (z as nat) < (z as nat));
            assert((half_result as nat) < (z as nat));
            // Since z is u8, we have z <= 255
            assert(z <= 255u8);
            assert((z as nat) <= 255);
            // Therefore half_result < z <= 255, so half_result < 256
            assert((half_result as nat) < 256);
            // Now we can prove the multiplication bound
            assert((half_result as nat) * (half_result as nat) < 256 * 256);
            assert(256 * 256 == 65536);
        }
        let squared = ((half_result as u16) * (half_result as u16)) % (z as u16);
        squared as u8
    } else {
        // y is odd, so y = 2 * (y/2) + 1
        let half_y = y / 2;
        proof {
            assert(n >= 1);
            assert((half_y as nat) < exp_int(2nat, n as nat));
        }
        let half_result = mod_exp_int(x, half_y, (n - 1) as u8, z);
        // half_result == exp_int(x, half_y) % z < z (by postcondition and modulo property)
        proof {
            assert((half_result as nat) == exp_int(x as nat, half_y as nat) % (z as nat));
            lemma_mod_bound(exp_int(x as nat, half_y as nat), z as nat);
            assert(exp_int(x as nat, half_y as nat) % (z as nat) < (z as nat));
            assert((half_result as nat) < (z as nat));
            // Since z is u8, we have z <= 255
            assert(z <= 255u8);
            assert((z as nat) <= 255);
            // Therefore half_result < z <= 255, so half_result < 256
            assert((half_result as nat) < 256);
            // Now we can prove the multiplication bound
            assert((half_result as nat) * (half_result as nat) < 256 * 256);
            assert(256 * 256 == 65536);
        }
        let squared = ((half_result as u16) * (half_result as u16)) % (z as u16);
        let result = ((squared as u16) * (x as u16)) % (z as u16);
        result as u8
    }
}
// </vc-code>


}

fn main() {}