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
/* helper modified by LLM (iteration 10): fixed parameter type in pow2_halving lemma */
proof fn lemma_exp_base_cases(base: nat)
{
    // Base cases are established by definition of exp_int
}

proof fn lemma_exp_double_specific(base: nat, exp: nat)
    requires exp > 0
    ensures exp_int(base, 2 * exp) == exp_int(base, exp) * exp_int(base, exp)
    decreases exp
{
    if exp == 1 {
        // For exp = 1: exp_int(base, 2*1) = exp_int(base, 2) = base * exp_int(base, 1) = base * base
        // And exp_int(base, 1) * exp_int(base, 1) = base * base
    } else {
        // Use induction on smaller exponent
        lemma_exp_double_specific(base, (exp - 1) as nat);
        // exp_int(base, 2*exp) = base^(2*exp) = base^2 * base^(2*(exp-1))
        // By induction: base^(2*(exp-1)) = (base^(exp-1))^2
        // So base^(2*exp) = base^2 * (base^(exp-1))^2 = (base * base^(exp-1))^2 = (base^exp)^2
    }
}

proof fn lemma_pow2_halving(n: nat)
    requires n > 0
    ensures exp_int(2, (n - 1) as nat) * 2 == exp_int(2, n)
    decreases n
{
    if n == 1 {
        // exp_int(2, 0) * 2 = 1 * 2 = 2 = exp_int(2, 1)
    } else {
        lemma_pow2_halving((n - 1) as nat);
    }
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
{
    /* code modified by LLM (iteration 10): fixed precondition check and overflow handling */
    if n == 0 {
        proof {
            assert(y as nat == exp_int(2, 0));
            assert(y == 1);
            assert(exp_int(x as nat, 1) == x as nat);
        }
        (x % z)
    } else {
        let half_y = y / 2;
        proof {
            lemma_pow2_halving(n as nat);
            assert(half_y as nat > 0);
        }
        let half_exp = mod_exp_pow2_int(x, half_y, n - 1, z);
        proof {
            lemma_exp_double_specific(x as nat, half_y as nat);
            assert(exp_int(x as nat, y as nat) == exp_int(x as nat, half_y as nat) * exp_int(x as nat, half_y as nat));
        }
        let result_u16 = ((half_exp as u16) * (half_exp as u16)) % (z as u16);
        proof {
            assert(result_u16 < z as u16);
            assert(result_u16 <= 255);
        }
        result_u16 as u8
    }
}
// </vc-code>


}

fn main() {}