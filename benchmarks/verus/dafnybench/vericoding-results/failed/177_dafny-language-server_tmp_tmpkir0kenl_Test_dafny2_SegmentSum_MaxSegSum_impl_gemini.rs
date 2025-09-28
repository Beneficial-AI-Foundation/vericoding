// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum(a: Seq<int>, s: int, t: int) -> int
    recommends 0 <= s <= t <= a.len()
    decreases t - s when 0 <= s <= t <= a.len()
{
    if s == t { 0 } else { sum(a, s, t-1) + a[t-1] }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): No functional changes in this iteration. */
proof fn sum_split(a: Seq<int>, i: int, j: int, k: int)
    requires
        0 <= i <= j <= k <= a.len(),
    ensures
        sum(a, i, k) == sum(a, i, j) + sum(a, j, k),
    decreases k - j
{
    if j < k {
        sum_split(a, i, j, k - 1);
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
    /* code modified by LLM (iteration 2): Fixed type mismatches by casting integer literals to int. */
    let n = a.len();
    let mut k: usize = 0;
    let mut m: usize = 0;
    let mut max_sum: int = 0 as int;

    let mut i: usize = 0;
    while i <= n
        invariant
            0 <= i <= n,
            0 <= k <= m <= n,
            max_sum == sum(a@, k as int, m as int),
            forall |p: int, q: int| 0 <= p < i && p <= q <= (a.len() as int) ==> sum(a@, p, q) <= max_sum,
        decreases n - i
    {
        let mut current_sum: int = 0 as int;
        let mut j: usize = i;
        while j <= n
            invariant
                i <= j <= n,
                current_sum == sum(a@, i as int, j as int),
                0 <= k <= m <= n,
                max_sum == sum(a@, k as int, m as int),
                forall |p: int, q: int| (0 <= p < i && p <= q <= (a.len() as int)) ==> sum(a@, p, q) <= max_sum,
                forall |r: int| i <= r < j ==> sum(a@, i as int, r) <= max_sum,
            decreases n - j
        {
            if current_sum > max_sum {
                max_sum = current_sum;
                k = i;
                m = j;
            }
            
            if j < n {
                current_sum = current_sum + a[j];
            }
            j = j + 1;
        }
        i = i + 1;
    }
    (k, m)
}
// </vc-code>

}
fn main() {}