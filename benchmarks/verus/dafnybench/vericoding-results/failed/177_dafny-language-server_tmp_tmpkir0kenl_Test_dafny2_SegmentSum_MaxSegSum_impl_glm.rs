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
spec fn sum_helper(a: Seq<int>, s: int, t: int) -> int
    recommends 0 <= s <= t <= a.len()
    decreases t - s
{
    if s == t {
        0
    } else {
        sum_helper(a, s, t - 1) + a[t - 1]
    }
}

lemma sum_lemma(a: Seq<int>, p: int, q: int, r: int)
    requires 0 <= p <= q <= r <= a.len()
    ensures sum_helper(a, p, r) == sum_helper(a, p, q) + sum_helper(a, q, r)
    decreases r - q
{
    if q == r {
        assert(sum_helper(a, p, r) == sum_helper(a, p, q));
    } else {
        sum_lemma(a, p, q, r - 1);
        assert(sum_helper(a, p, r) == sum_helper(a, p, r - 1) + a[r - 1]);
        assert(sum_helper(a, p, r - 1) == sum_helper(a, p, q) + sum_helper(a, q, r - 1));
        assert(sum_helper(a, q, r) == sum_helper(a, q, r - 1) + a[r - 1]);
    }
}

proof fn max_seg_sum_helper(a: Seq<int>)
    ensures exists |k: int, m: int| 0 <= k <= m <= a.len() && 
        forall |p: int, q: int| 0 <= p <= q <= a.len() ==> sum_helper(a, p, q) <= sum_helper(a, k, m)
{
    if a.len() == 0 {
        assert(forall |p: int, q: int| 0 <= p <= q <= 0 ==> sum_helper(a, p, q) <= sum_helper(a, 0, 0));
    } else {
        let (k, m) = max_seg_sum_helper(a.subrange(0, a.len() - 1));
        if sum_helper(a, k, a.len()) >= sum_helper(a, k, m) {
            assert(sum_helper(a, k, a.len()) == sum_helper(a, k, a.len() - 1) + a[a.len() - 1]);
            assert(sum_helper(a, k, a.len() - 1) == sum_helper(a.subrange(0, a.len() - 1), k, a.len() - 1));
            assert(forall |p: int, q: int| 0 <= p <= q <= a.len() ==> {
                if q < a.len() {
                    sum_helper(a, p, q) == sum_helper(a.subrange(0, a.len() - 1), p, q)
                } else if p < a.len() {
                    sum_lemma(a, p, a.len() - 1, q);
                    sum_helper(a, p, q) == sum_helper(a, p, a.len() - 1) + sum_helper(a, a.len() - 1, q)
                } else {
                    sum_helper(a, p, q) == sum_helper(a, a.len() - 1, q)
                }
            });
        } else {
            assert(sum_helper(a, k, m) == sum_helper(a.subrange(0, a.len() - 1), k, m));
            assert(forall |p: int, q: int| 0 <= p <= q <= a.len() ==> {
                if q < a.len() {
                    sum_helper(a, p, q) == sum_helper(a.subrange(0, a.len() - 1), p, q)
                } else if p < a.len() {
                    sum_lemma(a, p, a.len() - 1, q);
                    sum_helper(a, p, q) == sum_helper(a, p, a.len() - 1) + sum_helper(a, a.len() - 1, q)
                } else {
                    sum_helper(a, p, q) == sum_helper(a, a.len() - 1, q)
                }
            });
        }
    }
}

proof fn sum_eq(a: Seq<int>, s: int, t: int)
    requires 0 <= s <= t <= a.len()
    ensures sum(a, s, t) == sum_helper(a, s, t)
    decreases t - s
{
    if s == t {
        assert(sum(a, s, t) == 0);
        assert(sum_helper(a, s, t) == 0);
    } else {
        sum_eq(a, s, t - 1);
        assert(sum(a, s, t) == sum(a, s, t - 1) + a[t - 1]);
        assert(sum_helper(a, s, t) == sum_helper(a, s, t - 1) + a[t - 1]);
    }
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
    let n = a.len();
    if n == 0 {
        return (0, 0);
    }
    
    let mut max_sum: int = 0;
    let mut start: usize = 0;
    let mut end: usize = 0;
    let mut current_sum: int = 0;
    let mut current_start: usize = 0;
    
    for i in 0..n
        invariant
            0 <= current_start <= i <= n,
            0 <= start <= end <= i,
            max_sum == sum(a@, start as int, end as int),
            current_sum == sum(a@, current_start as int, i as int),
            forall |p: int, q: int| 0 <= p <= q <= i ==> sum(a@, p, q) <= max_sum,
    {
        if current_sum + a[i] > a[i] {
            current_sum = current_sum + a[i];
        } else {
            current_sum = a[i];
            current_start = i;
        }
        
        if current_sum > max_sum {
            max_sum = current_sum;
            start = current_start;
            end = i + 1;
        }
    }
    
    proof {
        assert forall |p: int, q: int| 0 <= p <= q <= n implies sum(a@, p, q) <= max_sum by {
            if q < n {
                // Case 1: q < n (already handled by loop invariant)
                assert(sum(a@, p, q) <= max_sum);
            } else if p < n {
                // Case 2: p < n <= q
                sum_lemma(a@, p, n as int, q);
                assert(sum(a@, p, q) == sum(a@, p, n) + sum(a@, n, q));
                assert(sum(a@, p, n) <= max_sum);
                assert(sum(a@, n, q) == 0);
            } else {
                // Case 3: n <= p <= q
                assert(sum(a@, p, q) == 0);
                assert(0 <= max_sum);
            }
        }
    }
    
    (start, end)
}
// </vc-code>

fn main() {}

}