// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn cube(n: int) -> int {
        n * n * n
}
    
    // </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed cube_monotonic proof */
spec fn is_perfect_cube(n: u8) -> bool {
    exists|k: int| 0 <= k <= n as int && n as int == cube(k)
}

proof fn cube_monotonic()
    ensures
        forall|k: int, l: int| 0 <= k <= l ==> cube(k) <= cube(l),
{
    assert forall|k: int, l: int| 0 <= k <= l implies cube(k) <= cube(l) by {
        if k < l {
            assert(cube(k) < cube(l));
        } else if k == l {
            assert(cube(k) == cube(l));
        }
    };
}
// </vc-helpers>

// <vc-spec>
fn is_cube(n: u8) -> (r: bool)
    ensures r == exists|k: int| 0 <= k <= n as int && n as int == cube(k)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed ghost variable declaration syntax */
    let n_int: int = n as int;
    let mut k: u8 = 0;
    while (k as int) <= n_int
        invariant
            0 <= k as int <= n_int + 1,
            forall|i: int| 0 <= i < k as int ==> cube(i) != n_int,
        decreases (n_int - (k as int)),
    {
        if cube(k as int) == n_int {
            return true;
        }
        k = k + 1;
    }
    false
}
// </vc-code>


}

fn main() {}