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
proof fn mod_exp_lemma(x: nat, y: nat, z: nat) -> (res: nat)
    requires
        z > 1,
    ensures res == exp_int(x, y) % z
    decreases y
{
    /* helper modified by LLM (iteration 10): fixed recursive lemma with proper base case */
    if y == 0 {
        1
    } else {
        let prev = mod_exp_lemma(x, (y - 1) as nat, z);
        (x * prev) % z
    }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp_int(x: u64, y: u64, n: u64, z: u64) -> (res: u64)
    requires 
        y < exp_int(x as nat, y as nat),
        z > 1,
    ensures res as nat == exp_int(x as nat, y as nat) % (z as nat)
    decreases n
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): fixed base case and recursive call handling */
    if y == 0 {
        1u64
    } else {
        let prev = mod_exp_int(x, y - 1, n - 1, z);
        (x * prev) % z
    }
}
// </vc-code>


}

fn main() {}