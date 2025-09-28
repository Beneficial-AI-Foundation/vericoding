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
/* helper modified by LLM (iteration 10): simplified lemma to focus on core property */
proof fn lemma_exp_positive(x: nat, y: nat)
    requires x >= 1
    ensures exp_int(x, y) >= 1
    decreases y
{
    if y == 0 {
        assert(exp_int(x, y) == 1);
    } else {
        lemma_exp_positive(x, (y - 1) as nat);
        assert(exp_int(x, y) == x * exp_int(x, (y - 1) as nat));
        assert(exp_int(x, (y - 1) as nat) >= 1);
        assert(x >= 1);
        assert(x * exp_int(x, (y - 1) as nat) >= 1);
    }
}

proof fn lemma_y_bounds(x: u64, y: u64)
    requires x >= 1, y >= 1, y < exp_int(x as nat, y as nat)
    ensures (y - 1) < exp_int(x as nat, (y - 1) as nat)
{
    if y == 1 {
        assert(y - 1 == 0);
        assert(exp_int(x as nat, 0) == 1);
        assert(0 < 1);
    } else {
        assert(y >= 2);
        assert(exp_int(x as nat, y as nat) == (x as nat) * exp_int(x as nat, (y - 1) as nat));
        lemma_exp_positive(x as nat, (y - 1) as nat);
        assert(exp_int(x as nat, (y - 1) as nat) >= 1);
        assert((x as nat) * exp_int(x as nat, (y - 1) as nat) >= x as nat);
        assert(y < (x as nat) * exp_int(x as nat, (y - 1) as nat));
        assert(y - 1 < y);
        assert((y - 1) < exp_int(x as nat, (y - 1) as nat));
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
    /* code modified by LLM (iteration 10): fix assertion syntax error */
    if y == 0 {
        1 % z
    } else {
        proof {
            lemma_y_bounds(x, y);
        }
        let rest = mod_exp_int(x, y - 1, if n > 0 { n - 1 } else { 0 }, z);
        proof {
            assert(rest < z);
            assert((x as nat) * (rest as nat) < (x as nat) * (z as nat));
            assert(x as u128 <= u64::MAX as u128);
            assert(rest as u128 <= u64::MAX as u128);
            assert((x as u128 * rest as u128) <= (u64::MAX as u128 * u64::MAX as u128));
        }
        let result = (x as u128 * rest as u128) % (z as u128);
        result as u64
    }
}
// </vc-code>


}

fn main() {}