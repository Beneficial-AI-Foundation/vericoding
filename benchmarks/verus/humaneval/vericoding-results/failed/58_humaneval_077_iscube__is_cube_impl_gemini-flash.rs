// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn cube(n: int) -> int {
        n * n * n
}
    
    // </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_cube(n: u8) -> (r: bool)
    ensures r == exists|k: int| 0 <= k <= n as int && n as int == cube(k)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type errors by casting to `int` for multiplication */
    let ghost n_int: int = n as int;
    let mut k: u8 = 0;
    while (k as int).checked_pow(3).unwrap_or(0) <= n as int
        invariant
            0 <= k,
            k <= 255,
            k as int <= 256,
            forall|j: int| 0 <= j < k as int ==> j * j * j != n_int,
        decreases n_int - (k as int) * (k as int) * (k as int)
    {
        proof {
            if k as int * k as int * k as int <= n_int && k >= 0 && k as int <= 256 {
                assert((k as int + 1) * (k as int + 1) * (k as int + 1) <= 343);
            }
        }

        if (k as int) * (k as int) * (k as int) == n_int {
            return true;
        }
        k = k + 1;
    }
    false
}
// </vc-code>


}

fn main() {}