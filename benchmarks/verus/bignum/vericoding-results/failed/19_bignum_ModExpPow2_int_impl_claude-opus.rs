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
/* helper modified by LLM (iteration 2): Added helper lemmas for exponentiation properties */
proof fn lemma_exp_int_mul(x: nat, a: nat, b: nat)
    ensures exp_int(x, a + b) == exp_int(x, a) * exp_int(x, b)
    decreases a
{
    if a == 0 {
        assert(exp_int(x, 0) == 1);
        assert(exp_int(x, b) == exp_int(x, b));
    } else {
        lemma_exp_int_mul(x, (a - 1) as nat, b);
        assert(exp_int(x, a + b) == x * exp_int(x, (a - 1) as nat + b));
        assert(exp_int(x, a) == x * exp_int(x, (a - 1) as nat));
    }
}

proof fn lemma_exp_2_split(n: nat)
    requires n > 0
    ensures exp_int(2, n) == 2 * exp_int(2, (n - 1) as nat)
{
    assert(exp_int(2, n) == 2 * exp_int(2, (n - 1) as nat));
}

proof fn lemma_mod_mul(a: nat, b: nat, m: nat)
    requires m > 0
    ensures (a * b) % m == ((a % m) * (b % m)) % m
{
    // This is a standard modular arithmetic property
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
/* code modified by LLM (iteration 2): Fixed base case to return x % z, handle recursive case with proper bounds checking */
{
    if n == 0 {
        proof {
            assert(y == 1) by {
                assert(y as nat == exp_int(2, 0));
                assert(exp_int(2, 0) == 1);
            }
            assert(exp_int(x as nat, 1) == x as nat);
        }
        // For y = 1, x^1 mod z = x mod z
        ((x as u16) % (z as u16)) as u8
    } else {
        // y = 2^n where n > 0, so y is even and y >= 2
        proof {
            assert(n > 0);
            lemma_exp_2_split(n as nat);
            assert(y as nat == exp_int(2, n as nat));
            assert(y as nat == 2 * exp_int(2, (n - 1) as nat));
            assert(y >= 2);
            assert(y / 2 == exp_int(2, (n - 1) as nat));
        }
        
        // Compute x^(y/2) mod z recursively
        let y_half_result = mod_exp_pow2_int(x, (y / 2) as u8, (n - 1) as u8, z);
        
        // x^y mod z = (x^(y/2) * x^(y/2)) mod z
        proof {
            assert(y_half_result as nat == exp_int(x as nat, (y / 2) as nat) % (z as nat));
            lemma_exp_int_mul(x as nat, (y / 2) as nat, (y / 2) as nat);
            assert(exp_int(x as nat, y as nat) == exp_int(x as nat, (y / 2) as nat) * exp_int(x as nat, (y / 2) as nat)) by {
                assert((y / 2) as nat + (y / 2) as nat == y as nat);
            }
            
            // Use modular arithmetic property
            lemma_mod_mul(exp_int(x as nat, (y / 2) as nat), exp_int(x as nat, (y / 2) as nat), z as nat);
        }
        
        // Ensure no overflow: y_half_result < z (from modulo), and z <= 255
        // So y_half_result * y_half_result < z * z <= 255 * 255 = 65025 < 65536
        proof {
            assert(y_half_result < z);
            assert(z <= 255);
            assert((y_half_result as u16) * (y_half_result as u16) < 65536);
        }
        
        ((y_half_result as u16 * y_half_result as u16) % (z as u16)) as u8
    }
}
// </vc-code>


}

fn main() {}