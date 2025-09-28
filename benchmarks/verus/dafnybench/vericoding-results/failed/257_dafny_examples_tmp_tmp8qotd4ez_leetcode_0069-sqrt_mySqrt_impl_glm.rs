use vstd::prelude::*;

verus! {

// Author: Shaobo He

spec fn sqrt(x: int, r: int) -> bool {
    r * r <= x && (r + 1) * (r + 1) > x
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::exec_allows_no_decreases_clause]
fn mySqrt(x: int) -> (res: int)
    requires 0 <= x,
    ensures sqrt(x, res),
// </vc-spec>
// <vc-code>
{
    let mut low = 0;
    let mut high = x + 1;
    
    while low < high
        invariant
            0 <= low <= high,
            high <= x + 1,
            forall|i: int| 0 <= i < low ==> i * i <= x,
            forall|i: int| high <= i <= x + 1 ==> i * i > x,
    {
        let mid = low + (high - low) / 2;
        if mid * mid <= x {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    
    let res = low - 1;
    res
}
// </vc-code>

fn main() {
}

}