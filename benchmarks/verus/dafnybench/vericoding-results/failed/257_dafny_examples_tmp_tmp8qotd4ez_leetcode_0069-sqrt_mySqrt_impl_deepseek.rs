use vstd::prelude::*;

verus! {

// Author: Shaobo He

spec fn sqrt(x: int, r: int) -> bool {
    r * r <= x && (r + 1) * (r + 1) > x
}

// <vc-helpers>
proof fn lemma_sqrt_monotonic(x: int, r1: int, r2: int)
    requires
        0 <= x,
        sqrt(x, r1),
        sqrt(x, r2),
    ensures
        r1 == r2,
{
    if r1 < r2 {
        assert((r1 + 1) * (r1 + 1) <= r2 * r2);
        assert((r1 + 1) * (r1 + 1) <= x);
    } else if r1 > r2 {
        assert((r2 + 1) * (r2 + 1) <= r1 * r1);
        assert((r2 + 1) * (r2 + 1) <= x);
    }
}

spec fn is_sqrt_candidate(x: int, r: int) -> bool {
    &&& 0 <= r
    &&& r <= x
    &&& r * r <= x
}

proof fn lemma_sqrt_exists(x: int, r: int)
    requires
        0 <= x,
        is_sqrt_candidate(x, r),
    ensures
        exists|res: int| sqrt(x, res),
{
}

proof fn lemma_sqrt_bounds(x: int, r: int)
    requires
        0 <= x,
        is_sqrt_candidate(x, r),
    ensures
        exists|res: int| sqrt(x, res) && res >= r,
{
}

proof fn lemma_sqrt_candidate_monotonic(x: int, r1: int, r2: int)
    requires
        0 <= x,
        0 <= r1 <= r2,
        is_sqrt_candidate(x, r2),
    ensures
        is_sqrt_candidate(x, r1),
{
}

proof fn lemma_mid_bounds(low: int, high: int)
    requires
        0 <= low <= high,
    ensures
        low <= low + (high - low) / 2 <= high,
{
}

proof fn lemma_range_split(x: int, low: int, mid: int, high: int)
    requires
        0 <= low <= mid <= high,
    ensures
        (forall|i: int| low <= i <= high ==> is_sqrt_candidate(x, i)) ==>
        (forall|i: int| low <= i <= mid ==> is_sqrt_candidate(x, i)) &&
        (forall|i: int| mid <= i <= high ==> is_sqrt_candidate(x, i)),
{
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
    let mut low: int = 0 as int;
    let mut high: int = x + 1;
    let mut res: int = 0 as int;
    
    while low <= high
        invariant
            0 <= low <= high <= x + 1,
            is_sqrt_candidate(x, low),
            forall|i: int| low <= i <= high ==> is_sqrt_candidate(x, i),
            exists|r: int| low <= r <= high && sqrt(x, r),
            res == if low > 0 { low - 1 } else { 0 },
            sqrt(x, res),
    {
        let mid: int = low + (high - low) / 2;
        let mid_sq = mid * mid;
        
        if mid_sq <= x {
            proof {
                lemma_sqrt_candidate_monotonic(x, low, mid);
                lemma_range_split(x, low, mid, high);
                assert(forall|i: int| mid <= i <= high ==> is_sqrt_candidate(x, i));
                lemma_sqrt_bounds(x, mid);
                assert(exists|r: int| mid <= r <= high && sqrt(x, r));
            }
            res = mid;
            low = mid + 1;
        } else {
            proof {
                lemma_range_split(x, low, mid, high);
                assert(forall|i: int| low <= i <= mid ==> is_sqrt_candidate(x, i));
            }
            high = mid - 1;
        }
    }
    
    res
}
// </vc-code>

fn main() {
}

}