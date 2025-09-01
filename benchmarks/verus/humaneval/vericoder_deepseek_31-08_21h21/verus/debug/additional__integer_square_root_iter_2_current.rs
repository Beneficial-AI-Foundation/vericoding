use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn sqrt_spec(n: int, r: int) -> bool {
    &&& 0 <= r*r
    &&& r*r <= n
    &&& n < (r+1)*(r+1)
}

proof fn sqrt_exists(n: int)
    requires n >= 1
    ensures exists|r: int| sqrt_spec(n, r)
{
    let mut i: int = 0;
    while i <= n
        invariant
            0 <= i <= n+1,
            forall|j: int| 0 <= j < i ==> !sqrt_spec(n, j)
    {
        if i*i <= n && n < (i+1)*(i+1) {
            assert(sqrt_spec(n, i));
            return;
        }
        i = i + 1;
    }
}

proof fn monotonic_squares(a: int, b: int)
    requires 0 <= a <= b
    ensures a*a <= b*b
{
}

proof fn square_increment(a: int)
    requires 0 <= a
    ensures (a+1)*(a+1) == a*a + 2*a + 1
{
}
// </vc-helpers>

// <vc-spec>
fn integer_square_root(n: i32) -> (result: i32)
    // pre-conditions-start
    requires
        n >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= result * result,
        result * result <= n,
        n < (result + 1) * (result + 1)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    proof {
        sqrt_exists(n as int);
    }
    
    let mut low: i32 = 0;
    let mut high: i32 = n;
    let mut result: i32 = 0;
    
    while low <= high
        invariant
            0 <= low <= high + 1,
            high <= n,
            forall|i: int| 0 <= i < low as int ==> (i as i32)*(i as i32) <= n,
            forall|j: int| high as int < j <= n as int ==> n < (j as i32)*(j as i32),
            exists|r: int| low as int <= r <= high as int && sqrt_spec(n as int, r)
    {
        let mid = low + (high - low) / 2;
        let mid_sq = mid * mid;
        
        if mid_sq <= n {
            proof {
                monotonic_squares(low as int, mid as int);
                square_increment(mid as int);
            }
            if n < (mid + 1) * (mid + 1) {
                result = mid;
                break;
            } else {
                low = mid + 1;
            }
        } else {
            high = mid - 1;
        }
    }
    
    proof {
        assert(sqrt_spec(n as int, result as int));
    }
    
    result
}
// </vc-code>

fn main() {}
}