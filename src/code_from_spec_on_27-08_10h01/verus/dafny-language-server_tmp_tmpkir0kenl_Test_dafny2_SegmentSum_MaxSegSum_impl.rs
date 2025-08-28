// RUN: %verus "%s"

use vstd::prelude::*;

verus! {

spec fn sum(a: Seq<int>, s: int, t: int) -> int
    recommends 0 <= s <= t <= a.len()
    decreases t - s when 0 <= s <= t <= a.len()
{
    if s == t { 0 } else { sum(a, s, t-1) + a[t-1] }
}

// <vc-helpers>
spec fn max_sum_ending_at(a: Seq<int>, i: int) -> int
    recommends 0 <= i <= a.len()
{
    if i == 0 {
        0
    } else {
        let max_ending_prev = max_sum_ending_at(a, i - 1);
        if max_ending_prev + a[i - 1] > 0 {
            max_ending_prev + a[i - 1]
        } else {
            0
        }
    }
}

spec fn max_sum_in_range(a: Seq<int>, start: int, end: int) -> int
    recommends 0 <= start <= end <= a.len()
    decreases end - start when 0 <= start <= end <= a.len()
{
    if start == end {
        0
    } else {
        let max_rest = max_sum_in_range(a, start, end - 1);
        let max_ending_here = max_sum_ending_at(a, end);
        if max_rest > max_ending_here {
            max_rest
        } else {
            max_ending_here
        }
    }
}

proof fn sum_property_empty(a: Seq<int>)
    ensures sum(a, 0, 0) == 0
{
}

proof fn sum_property_extends(a: Seq<int>, s: int, t: int)
    requires 0 <= s < t <= a.len()
    ensures sum(a, s, t) == sum(a, s, t-1) + a[t-1]
{
}

proof fn kadane_correctness(a: Seq<int>, n: int)
    requires 0 <= n <= a.len()
    ensures exists |k: int, m: int| 0 <= k <= m <= n && 
        sum(a, k, m) == max_sum_in_range(a, 0, n) &&
        forall |p: int, q: int| 0 <= p <= q <= n ==> 
            sum(a, p, q) <= sum(a, k, m)
    decreases n
{
    if n == 0 {
    } else {
        kadane_correctness(a, n - 1);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn max_seg_sum(a: &Vec<int>) -> (result: (usize, usize))
    ensures ({
        let (k, m) = result;
        &&& k <= m <= a.len()
        &&& forall |p: int, q: int| 0 <= p <= q <= a.len() ==> 
            sum(a@, p, q) <= sum(a@, k as int, m as int)
    })
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if a.len() == 0 {
        return (0, 0);
    }
    
    let mut max_so_far: int = 0int;
    let mut max_ending_here: int = 0int;
    let mut start = 0;
    let mut end = 0;
    let mut temp_start = 0;
    
    let mut i = 0;
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            0 <= start <= end <= i,
            0 <= temp_start <= i,
            max_so_far >= 0,
            max_ending_here >= 0,
            sum(a@, start as int, end as int) == max_so_far,
            forall |p: int, q: int| 0 <= p <= q <= i ==> sum(a@, p, q) <= max_so_far
    {
        max_ending_here = max_ending_here + a[i];
        
        if max_ending_here > max_so_far {
            max_so_far = max_ending_here;
            start = temp_start;
            end = i + 1;
        }
        
        if max_ending_here < 0int {
            max_ending_here = 0int;
            temp_start = i + 1;
        }
        
        i += 1;
    }
    
    proof {
        kadane_correctness(a@, a.len() as int);
    }
    
    (start, end)
}
// </vc-code>

fn main() {}

}