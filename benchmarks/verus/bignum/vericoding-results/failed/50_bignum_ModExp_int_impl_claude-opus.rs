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
proof fn lemma_exp_zero(x: nat)
    ensures exp_int(x, 0) == 1
{
}

proof fn lemma_exp_succ(x: nat, y: nat)
    ensures exp_int(x, y + 1) == x * exp_int(x, y)
{
}

/* helper modified by LLM (iteration 10): Fixed type casting for nat parameters */
proof fn lemma_mod_mul(a: nat, b: nat, m: nat)
    requires m > 0
    ensures (a * b) % m == ((a % m) * (b % m)) % m
{
    vstd::arithmetic::div_mod::lemma_mul_mod_noop_general(a as int, b as int, m as int);
}

/* helper modified by LLM (iteration 10): Fixed nat type casting in recursive call */
proof fn lemma_exp_growth(x: nat, y: nat)
    requires x >= 2, y > 0
    ensures y <= exp_int(x, y)
    decreases y
{
    if y == 1 {
        assert(exp_int(x, 1) == x);
        assert(x >= 2);
    } else {
        lemma_exp_growth(x, (y - 1) as nat);
        assert(exp_int(x, y) == x * exp_int(x, (y - 1) as nat));
        assert((y - 1) as nat <= exp_int(x, (y - 1) as nat));
        assert(exp_int(x, y) >= 2 * ((y - 1) as nat));
        assert(exp_int(x, y) >= y);
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
    /* code modified by LLM (iteration 10): Fixed nat type casting in proof block */
    if y == 0 {
        proof {
            lemma_exp_zero(x as nat);
        }
        1
    } else {
        // For recursive call, we need (y-1) < exp_int(x, y-1)
        proof {
            assert(y > 0);
            // From precondition: y < exp_int(x, y)
            // When x >= 2: exp_int(x, y-1) >= 2^(y-1) >= y-1
            // When x == 1: exp_int(1, y) = 1, so y < 1 means y = 0 (contradiction)
            // When x == 0: exp_int(0, y) = 0 for y > 0 (contradiction)
            if x >= 2 {
                // For x >= 2, exp_int grows exponentially
                lemma_exp_growth(x as nat, (y - 1) as nat);
                assert((y - 1) as nat <= exp_int(x as nat, (y - 1) as nat));
            } else if x == 1 {
                // x = 1 case: exp_int(1, k) = 1 for all k
                // Precondition y < exp_int(1, y) = 1 means y = 0
                // But we're in else branch, so y > 0, contradiction
                assert(exp_int(1, y as nat) == 1);
                assert(false);  // This case is impossible
            } else {
                // x = 0 case: exp_int(0, y) = 0 for y > 0
                // Precondition y < 0 is impossible
                assert(exp_int(0, y as nat) == 0);
                assert(false);  // This case is impossible
            }
        }
        
        let x_mod = (x % z) as u64;
        let sub_result = mod_exp_int(x, (y - 1) as u64, y - 1, z);
        
        proof {
            assert(exp_int(x as nat, y as nat) == (x as nat) * exp_int(x as nat, (y - 1) as nat));
            lemma_mod_mul(x as nat, exp_int(x as nat, (y - 1) as nat), z as nat);
            assert(sub_result as nat == exp_int(x as nat, (y - 1) as nat) % (z as nat));
            assert(exp_int(x as nat, y as nat) % (z as nat) == ((x as nat) * exp_int(x as nat, (y - 1) as nat)) % (z as nat));
            assert(((x as nat) * exp_int(x as nat, (y - 1) as nat)) % (z as nat) == (((x as nat) % (z as nat)) * (exp_int(x as nat, (y - 1) as nat) % (z as nat))) % (z as nat));
        }
        
        ((x_mod as u128 * sub_result as u128) % (z as u128)) as u64
    }
}
// </vc-code>


}

fn main() {}