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
    /* code modified by LLM (iteration 2): fixed compilation error by using executable arithmetic and added optimization */
    let mut k: u8 = 0;
    while k <= n
        invariant
            forall|i: int| 0 <= i < k as int ==> cube(i) != (n as int),
        decreases n - k
    {
        // Use a larger type to avoid overflow during calculation
        let k_cubed = (k as u64) * (k as u64) * (k as u64);
        if k_cubed == (n as u64) {
            return true;
        }
        
        if k_cubed > (n as u64) {
            return false;
        }
        
        if k == 255 {
            break;
        }
        k = k + 1;
    }
    
    false
}
// </vc-code>


}

fn main() {}