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
/* helper modified by LLM (iteration 5): Used u32 for multiplication to avoid overflow, added proof to verify postcondition */
fn mul_mod(a: u8, b: u8, m: u8) -> (result: u8)
    requires m > 0
    ensures result as nat == ((a as nat) * (b as nat)) % (m as nat)
{
    let ab: u32 = (a as u32) * (b as u32);
    let m_u32: u32 = m as u32;
    let mod_ab: u32 = ab % m_u32;
    let result: u8 = mod_ab as u8;
    proof {
        assert(mod_ab as nat == ((a as nat) * (b as nat)) % (m as nat)) by {
            assert(a as u32 as nat == a as nat);
            assert(b as u32 as nat == b as nat);
            assert(m as u32 as nat == m as nat);
            // u32 arithmetic within bounds matches nat
        }
    }
    result
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
/* code modified by LLM (iteration 5): Added assertion for exp_int base case to satisfy invariants */
{
    proof {
        assert(exp_int(2, 0) == 1);
    }
    let mut current: u8 = x % z;
    let mut i: u8 = 0;
    while i < n
        invariant
            i <= n,
            z > 0,
            current as nat == (exp_int(x as nat, exp_int(2, i as nat))) % (z as nat)
        decreases n - i
    {
        current = mul_mod(current, current, z);
        i = i + 1;
    }
    current
}
// </vc-code>


}

fn main() {}