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
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
fn A8Q1(y0: int, x: int) -> (z: int)
    requires y0 >= 0
    ensures z == power(x, y0)
// </vc-spec>
// <vc-code>
{
    let mut y: i32 = y0 as i32;
    let mut z: i32 = 1;
    let x_i32: i32 = x as i32;
    
    while y > 0
        invariant
            y >= 0,
            y0 >= 0,
            y <= y0,
            z as int * power(x, y as int) == power(x, y0),
    {
        z = z * x_i32;
        y = y - 1;
    }
    
    proof {
        assert(y == 0);
        assert(z as int * power(x, 0) == power(x, y0));
        assert(power(x, 0) == 1);
        assert(z as int == power(x, y0));
    }
    
    z as int
}
// </vc-code>

fn main() {}

}