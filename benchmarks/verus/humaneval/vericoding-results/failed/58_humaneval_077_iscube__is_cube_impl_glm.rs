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
    let mut k: int = 0;
    while k <= n as int
        invariant
            0 <= k <= n as int + 1,
            forall|i: int| 0 <= i < k ==> i*i*i != n as int,
        decreases (n as int + 1) - k
    {
        let cube_k = k * k * k;
        if cube_k == n as int {
            return true;
        }
        if cube_k > n as int {
            break;
        }
        k = k + 1;
    }
    false
}
// </vc-code>


}

fn main() {}