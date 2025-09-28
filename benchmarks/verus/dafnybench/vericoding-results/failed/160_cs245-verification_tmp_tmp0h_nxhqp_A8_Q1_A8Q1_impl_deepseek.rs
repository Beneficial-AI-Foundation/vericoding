use vstd::prelude::*;

verus! {

// A8Q1 — Steph Renee McIntyre
// Following the solutions from Carmen Bruni

// There is no definition for power, so this function will be used for validating that our imperative program is correct. This is just for Verus.
spec fn power(a: int, n: int) -> int //function for a to the power of n
    recommends 0 <= n
    decreases n when 0 <= n
{
    if n <= 0 { 1 } else { a * power(a, n - 1) }
}

/* Proof of implieds can be seen on LEARN.
    Note: If you are unconvinced, putting asserts for each condition will demonstrate the correctness of the statements. 
*/

// <vc-helpers>
proof fn lemma_power_zero(a: int)
    ensures
        power(a, 0) == 1,
{
}

proof fn lemma_power_successor(a: int, n: int)
    requires
        0 <= n,
    ensures
        power(a, n + 1) == a * power(a, n),
{
}

proof fn lemma_power_base(a: int, n: int)
    requires
        0 <= n,
    ensures
        power(1, n) == 1,
    decreases n,
{
    if n > 0 {
        lemma_power_base(a, n - 1);
    }
}

proof fn lemma_power_identity(a: int)
    ensures
        power(a, 0) == 1 && power(a, 1) == a,
{
}

spec fn invariant(y: int, z: int, x: int, y0: int) -> bool {
    z * power(x, y) == power(x, y0)
}
// </vc-helpers>

// <vc-spec>
fn A8Q1(y0: int, x: int) -> (z: int)
    requires y0 >= 0
    ensures z == power(x, y0)
// </vc-spec>
// <vc-code>
{
    let mut y: int = y0;
    let mut z: int = 1;
    
    while y > 0
        invariant
            0 <= y <= y0,
            z * power(x, y) == power(x, y0),
        decreases y,
    {
        y = y - 1;
        z = z * x;
        proof {
            lemma_power_successor(x, y);
        }        
    }
    
    proof {
        lemma_power_zero(x);
    }
    
    z
}
// </vc-code>

fn main() {}

}