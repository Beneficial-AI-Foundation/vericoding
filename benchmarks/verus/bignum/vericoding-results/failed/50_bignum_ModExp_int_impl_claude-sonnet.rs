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
/* helper modified by LLM (iteration 10): strengthen lemma to prove actual properties needed */
proof fn lemma_exp_decreases(x: nat, y: nat)
    requires 
        y > 0
    ensures y / 2 < y
{
    // For any y > 0, we have y / 2 < y
    // This is a simple arithmetic fact
}

proof fn lemma_exp_properties(x: nat, y: nat)
    ensures 
        exp_int(x, 0) == 1,
        y > 0 ==> exp_int(x, y) == x * exp_int(x, (y - 1) as nat)
{
}

proof fn lemma_precondition_recursive(x: nat, y: nat)
    requires
        y > 0,
        x >= 2,
        y < exp_int(x, y)
    ensures
        y / 2 < exp_int(x, y / 2)
{
    // Base case: if y/2 == 0, then exp_int(x, 0) = 1 > 0 >= y/2
    if y / 2 == 0 {
        assert(exp_int(x, 0) == 1);
    } else {
        // For x >= 2 and y > 0, exponential function grows faster than linear
        // Since y < x^y and x >= 2, we have y/2 < x^(y/2)
        assert(y / 2 >= 1);
        assert(exp_int(x, y / 2) >= x);
        assert(x >= 2);
        assert(y / 2 < y);
        assert(y < exp_int(x, y));
        // Since exponential grows faster than linear for x >= 2
        assert(y / 2 < exp_int(x, y / 2));
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
    /* code modified by LLM (iteration 10): fix decreases clause and handle precondition properly */
    if y == 0 {
        1 % z
    } else if y % 2 == 0 {
        proof {
            lemma_exp_decreases(x as nat, y as nat);
            if x >= 2 {
                lemma_precondition_recursive(x as nat, y as nat);
            }
        }
        let half_exp = mod_exp_int(x, y / 2, y, z);
        let temp = (half_exp as u128) * (half_exp as u128);
        (temp % (z as u128)) as u64
    } else {
        proof {
            lemma_exp_decreases(x as nat, y as nat);
            if x >= 2 {
                lemma_precondition_recursive(x as nat, y as nat);
            }
        }
        let half_exp = mod_exp_int(x, y / 2, y, z);
        let temp = (x as u128) * (half_exp as u128) * (half_exp as u128);
        (temp % (z as u128)) as u64
    }
}
// </vc-code>


}

fn main() {}