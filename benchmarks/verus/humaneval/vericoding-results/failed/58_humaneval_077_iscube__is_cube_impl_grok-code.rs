// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn cube(n: int) -> int {
        n * n * n
}
    
    // </vc-preamble>

// <vc-helpers>
spec fn cube(n: int) -> int {
    n * n * n
}
// </vc-helpers>

// <vc-spec>
fn is_cube(n: u8) -> (r: bool)
    ensures r == exists|k: int| 0 <= k <= n as int && n as int == cube(k)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation errors by using u64 for exec variables to replace int in ghost code-only usage */
    let mut k = 0u64;
    let nk = n as u64;
    while k <= 7u64 {
        let ck = k.checked_mul(k).unwrap_or(0).checked_mul(k).unwrap_or(0);
        if ck == nk {
            return true;
        }
        k += 1;
    }
    false
}
// </vc-code>


}

fn main() {}