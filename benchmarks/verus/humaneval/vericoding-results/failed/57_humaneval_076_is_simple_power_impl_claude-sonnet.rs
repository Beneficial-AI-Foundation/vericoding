// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn power(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 { 1 } else { x * power(x, (y - 1) as nat) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed lemma declaration syntax by adding exclamation mark */
lemma lemma_power_monotonic(x: nat, y1: nat, y2: nat)
    requires x > 1, y1 < y2
    ensures power(x, y1) < power(x, y2)
    decreases y2
{
    if y2 == 0 {
    } else if y1 == 0 {
        lemma_power_positive(x, y2 - 1);
    } else {
        lemma_power_monotonic(x, y1 - 1, y2 - 1);
    }
}

lemma lemma_power_positive(x: nat, y: nat)
    requires x > 0
    ensures power(x, y) > 0
    decreases y
{
}

lemma lemma_power_bounds(x: nat, y: nat)
    requires x > 1, y > 0
    ensures power(x, y) >= x
    decreases y
{
    if y == 1 {
    } else {
        lemma_power_bounds(x, y - 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn is_simple_power(x: u8, n: i8) -> (ans: bool)
    requires x > 0
    ensures ans <==> exists|y: nat| n as int == power(x as nat, y) as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type consistency and overflow handling */
    if n <= 0 {
        return n == 1;
    }
    
    let mut y = 0;
    let mut current_power = 1;
    
    while current_power < n as u32
        invariant
            current_power == power(x as nat, y),
            current_power <= n as u32,
            y <= 32,
        decreases 32 - y
    {
        if current_power > u32::MAX / (x as u32) {
            return false;
        }
        current_power = current_power * (x as u32);
        y = y + 1;
        
        if y > 32 {
            return false;
        }
    }
    
    current_power == n as u32
}
// </vc-code>


}

fn main() {}