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
/* helper modified by LLM (iteration 3): lemma to prove exponentiation step with correct properties */
proof fn lemma_exp_step(x: nat, i: nat, z: nat, current: nat)
    requires current == exp_int(x, exp_int(2, i)) % z,
        z > 0,
    ensures (current * current) % z == exp_int(x, exp_int(2, i+1)) % z
{
    // Prove that 2^(i+1) = 2 * 2^i
    assert(exp_int(2, i+1) == 2 * exp_int(2, i));
    
    // Prove that x^(2*a) = (x^a) * (x^a)
    assert(exp_int(x, 2 * exp_int(2, i)) == exp_int(x, exp_int(2, i)) * exp_int(x, exp_int(2, i)));
    
    // Use the requirement that current = x^(2^i) % z
    assert(current == exp_int(x, exp_int(2, i)) % z);
    
    // Therefore (current * current) % z = (x^(2^i) * x^(2^i)) % z
    assert((current * current) % z == (exp_int(x, exp_int(2, i)) * exp_int(x, exp_int(2, i))) % z);
    
    // And this equals x^(2^(i+1)) % z
    assert((exp_int(x, exp_int(2, i)) * exp_int(x, exp_int(2, i))) % z == exp_int(x, exp_int(2, i+1)) % z);
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
/* code modified by LLM (iteration 3): fixed overflow and assertion issues */
{
    let mut res = x % z;
    let mut i = 0;
    proof {
        assert(exp_int(2, 0) == 1);
        assert(exp_int(x as nat, 1) == x as nat);
        assert(res as nat == (x as nat) % (z as nat));
        assert((x as nat) % (z as nat) == exp_int(x as nat, 1) % (z as nat));
        assert(exp_int(x as nat, 1) % (z as nat) == exp_int(x as nat, exp_int(2, 0)) % (z as nat));
    }
    while i < n
        invariant
            res as nat == exp_int(x as nat, exp_int(2, i as nat)) % (z as nat),
            i <= n,
        decreases n - i
    {
        let res_u32 = res as u32;
        let z_u32 = z as u32;
        proof {
            assert(z > 0);
            assert(z_u32 > 0);
            assert(res_u32 <= 255);
        }
        let product = res_u32 * res_u32;
        proof {
            assert(product <= 65025);
        }
        let mod_val = product % z_u32;
        proof {
            assert(mod_val < z_u32);
            assert(mod_val <= 254);
        }
        let new_res = mod_val as u8;
        proof {
            lemma_exp_step(x as nat, i as nat, z as nat, res as nat);
            assert(new_res as nat == (res as nat * res as nat) % (z as nat));
            assert(new_res as nat == exp_int(x as nat, exp_int(2, i as nat + 1)) % (z as nat));
            assert(exp_int(2, i as nat + 1) == exp_int(2, (i+1) as nat));
            assert(new_res as nat == exp_int(x as nat, exp_int(2, (i+1) as nat)) % (z as nat));
        }
        res = new_res;
        i += 1;
    }
    res
}
// </vc-code>


}

fn main() {}