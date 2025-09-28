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
proof fn sum_succ(a: Seq<int>, s: int, t: int)
    requires 0 <= s && s <= t && (t + 1) <= (a.len() as int)
    ensures  sum(a, s, t + 1) == sum(a, s, t) + a@[t]
{
    if s == t {
        // sum(a, s, s) == 0 and sum(a, s, s+1) == a[s]
        assert(sum(a, s, t) == 0);
        assert(sum(a, s, t + 1) == a@[t]);
        assert(sum(a, s, t + 1) == sum(a, s, t) + a@[t]);
    } else {
        assert(sum(a, s, t + 1) == sum(a, s, t) + a@[t]);
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
    let n: usize = a.len();
    if n == 0 {
        return (0, 0);
    }

    let mut best_k: usize = 0;
    let mut best_m: usize = 0;
    let mut best_sum: int = 0;

    let mut s: usize = 0;
    while s < n
        invariant s <= n;
        invariant best_k <= best_m;
        invariant best_m <= n;
        invariant forall |p: int, q: int| (0 <= p && p <= q && q <= n as int && p < s as int) ==> #[trigger] (sum(a@, p, q) <= best_sum);
    {
        let mut t: usize = s;
        let mut curr: int = 0;
        // curr corresponds to sum(a, s, t)
        // Establish the loop invariant before entering inner loop:
        assert(curr == sum(a@, s as int, t as int));

        while t < n
            invariant s <= t && t <= n;
            invariant curr == sum(a@, s as int, t as int);
            invariant best_k <= best_m;
            invariant best_m <= n;
            invariant forall |p: int, q: int| (0 <= p && p <= q && q <= n as int && (p < s as int || (p == s as int && q <= t as int))) ==> #[trigger] (sum(a@, p, q) <= best_sum);
        {
            // old_t = t
            let old_t: usize = t;
            // update curr to include a[old_t]
            curr = curr + a@[old_t as int];
            // increment t, now curr should equal sum(a, s, t)
            t = t + 1;
            // Use lemma to relate sums
            proof {
                sum_succ(a@, s as int, old_t as int);
            }
            // If this new segment has larger sum, update best
            if curr > best_sum {
                best_sum = curr;
                best_k = s;
                best_m = t;
            }
        }

        // After inner loop, all segments starting at s have been considered.
        s = s + 1;
    }

    (best_k, best_m)
}
// </vc-code>

fn main() {}

}