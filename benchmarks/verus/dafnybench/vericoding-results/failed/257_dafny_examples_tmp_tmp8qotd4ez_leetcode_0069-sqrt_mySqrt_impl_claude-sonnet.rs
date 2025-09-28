use vstd::prelude::*;

verus! {

// Author: Shaobo He

spec fn sqrt(x: int, r: int) -> bool {
    r * r <= x && (r + 1) * (r + 1) > x
}

// <vc-helpers>
spec fn sqrt_invariant_holds(lo: int, hi: int, x: int) -> bool {
    0 <= lo <= hi + 1 &&
    hi <= x &&
    lo * lo <= x &&
    (hi + 1) * (hi + 1) > x
}
// </vc-helpers>

// <vc-spec>
#[verifier::exec_allows_no_decreases_clause]
fn mySqrt(x: int) -> (res: int)
    requires 0 <= x,
    ensures sqrt(x, res),
// </vc-spec>
// <vc-code>
{
    if x == 0 {
        return 0;
    }
    
    let mut lo = 0;
    let mut hi = x;
    
    while lo <= hi
        invariant 
            0 <= lo <= hi + 1,
            hi <= x,
            lo * lo <= x,
            (hi + 1) * (hi + 1) > x,
    {
        let mid = lo + (hi - lo) / 2;
        
        if mid * mid <= x {
            if (mid + 1) * (mid + 1) > x {
                return mid;
            }
            lo = mid + 1;
        } else {
            hi = mid - 1;
        }
    }
    
    hi
}
// </vc-code>

fn main() {
}

}