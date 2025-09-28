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
    /* code modified by LLM (iteration 3): use safe multiplication with overflow checks */
    let mut result = 1;
    let mut base = x % z;
    let mut exponent = y;

    while exponent > 0
        invariant
            (result as nat * exp_int(base as nat, exponent as nat)) % (z as nat) == exp_int(x as nat, y as nat) % (z as nat),
        decreases exponent
    {
        if exponent % 2 == 1 {
            // Safe multiplication: result * base % z
            if result > 0 && base > u64::MAX / result {
                // Fallback to addition loop for potential overflow
                let mut temp = 0;
                let mut i = 0;
                while i < result
                    invariant
                        temp as nat == (base as nat * i as nat) % (z as nat),
                        i <= result,
                    decreases result - i
                {
                    temp = (temp + base) % z;
                    i += 1;
                }
                result = temp;
            } else {
                result = (result * base) % z;
            }
        }
        
        // Safe squaring: base * base % z
        if base > 0 && base > u64::MAX / base {
            // Fallback to addition loop for potential overflow
            let mut temp = 0;
            let mut j = 0;
            while j < base
                invariant
                    temp as nat == (base as nat * j as nat) % (z as nat),
                    j <= base,
                decreases base - j
            {
                temp = (temp + base) % z;
                j += 1;
            }
            base = temp;
        } else {
            base = (base * base) % z;
        }
        
        exponent = exponent / 2;
    }

    result
}
// </vc-code>


}

fn main() {}