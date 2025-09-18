// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(xs: Seq<i32>, target: i32) -> nat {
    xs.filter(|x: i32| x == target).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): count_prefix over nat k */
spec fn count_prefix(s: Seq<i32>, target: i32, k: nat) -> nat
    requires
        k <= s.len(),
    decreases
        k,
{
    if k == 0 {
        0
    } else {
        let k1: nat = k - 1;
        count_prefix(s, target, k1) + (if s[k1] == target { 1 } else { 0 })
    }
}
// </vc-helpers>

// <vc-spec>
fn most_frequent(xs: Vec<i32>) -> (result: i32)
    requires xs.len() > 0,
    ensures
        xs@.contains(result),
        forall|x: i32| xs@.contains(x) ==> count_occurrences(xs@, x) <= count_occurrences(xs@, result),
        exists|first_idx: int| 
            0 <= first_idx < xs.len() && 
            xs[first_idx] == result && 
            count_occurrences(xs@, result) == count_occurrences(xs@, xs[first_idx]) &&
            forall|i: int| 0 <= i < first_idx ==> count_occurrences(xs@, xs[i]) < count_occurrences(xs@, result),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use usize indices and spec count_prefix with nat, avoid int/nat in runtime */
    let n: usize = xs.len();
    let mut best_idx: usize = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            best_idx < n,
            forall|j: usize| j < i ==> count_occurrences(xs@, xs@[j as nat]) <= count_occurrences(xs@, xs@[best_idx as nat]),
            forall|j: usize| j < best_idx ==> count_occurrences(xs@, xs@[j as nat]) < count_occurrences(xs@, xs@[best_idx as nat]),
        decreases n - i
    {
        let mut k: usize = 0;
        let mut cnt: usize = 0;
        while k < n
            invariant
                k <= n,
                cnt <= n,
                cnt as nat == count_prefix(xs@, xs@[i as nat], k as nat),
            decreases n - k
        {
            if xs[k] == xs[i] {
                cnt = cnt + 1;
            }
            k = k + 1;
        }

        let mut k2: usize = 0;
        let mut best_cnt: usize = 0;
        while k2 < n
            invariant
                k2 <= n,
                best_cnt <= n,
                best_cnt as nat == count_prefix(xs@, xs@[best_idx as nat], k2 as nat),
            decreases n - k2
        {
            if xs[k2] == xs[best_idx] {
                best_cnt = best_cnt + 1;
            }
            k2 = k2 + 1;
        }

        if cnt as nat > best_cnt as nat {
            best_idx = i;
        }

        i = i + 1;
    }

    let result = xs[best_idx];
    proof {
        assert(best_idx < n);
    }
    result
}
// </vc-code>

}
fn main() {}