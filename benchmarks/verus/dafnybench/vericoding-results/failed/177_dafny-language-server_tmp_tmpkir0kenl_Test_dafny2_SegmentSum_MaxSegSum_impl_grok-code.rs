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
fn sum_calc(a: &Vec<int>, s: usize, t: usize) -> (result: int)
    requires
        s <= t <= a.len(),
    ensures
        result == sum(a@, s as int, t as int)
{
    let mut res: i64 = 0;
    let mut i = s;
    while i < t
        invariant
            res as int == sum(a@, s as int, i as int),
            decreases t - i
    {
        res = res + a[i] as i64;
        i = i + 1;
        proof {
            assert(sum(a@, s as int, i as int) == sum(a@, s as int, (i - 1) as int) + a[(i - 1)]);
        }
    }
    res as int
}
// </vc-helpers>

// <vc-spec>
fn max_seg_sum(a: &Vec<int>) -> (result: (usize, usize))
    ensures ({
        let (k, m) = result;
        &&& k <= m <= a.len()
        &&& forall |p: int, q: int| 0 <= p <= q <= a.len() ==> 
            sum(a@, p, q) <= sum(a@, k as int, m as int)
    })
// </vc-spec>
// <vc-code>
{
    if a.is_empty() {
        return (0, 0);
    }
    let mut max_sum: i64 = 0;
    let mut best_k: usize = 0;
    let mut best_m: usize = 0;
    let mut start: usize = 0;
    let mut end: usize;
    while start < a.len()
        invariant
            0 <= best_k <= best_m <= a.len(),
            max_sum as int == sum(a@, best_k as int, best_m as int),
            forall |p: int, q: int| 0 <= p <= q <= a.len() && p < start ==> sum(a@, p, q) <= max_sum as int
    {
        end = start;
        while end <= a.len()
            invariant
                start <= end <= a.len(),
                forall |p: int, q: int| 0 <= p <= q <= a.len() && 
                    ((p < start) || (p == start && q <= end)) ==> 
                    sum(a@, p, q) <= max_sum as int
        {
            let s = sum_calc(a, start, end);
            if (s as i64) > max_sum {
                max_sum = s as i64;
                best_k = start;
                best_m = end;
            }
            if end < a.len() {
                end = end + 1;
            } else {
                break;
            }
        }
        if start < a.len() {
            start = start + 1;
        } else {
            break;
        }
    }
    (best_k, best_m)
}
// </vc-code>

fn main() {}

}