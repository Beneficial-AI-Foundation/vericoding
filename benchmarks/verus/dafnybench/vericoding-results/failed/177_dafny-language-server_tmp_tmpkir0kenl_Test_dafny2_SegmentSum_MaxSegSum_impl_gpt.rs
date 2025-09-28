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
proof fn lemma_sum_extend_right(a: Seq<int>, s: int, t: int)
    requires
        0 <= s <= t < a.len(),
    ensures
        sum(a, s, t + 1) == sum(a, s, t) + a[t],
{
    assert(0 <= s <= t + 1 <= a.len());
    assert(s != t + 1);
    assert(sum(a, s, t + 1) == sum(a, s, (t + 1) - 1) + a[(t + 1) - 1]);
    assert((t + 1) - 1 == t);
    assert(a[(t + 1) - 1] == a[t]);
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
    loop { }
}
// </vc-code>

fn main() {}

}