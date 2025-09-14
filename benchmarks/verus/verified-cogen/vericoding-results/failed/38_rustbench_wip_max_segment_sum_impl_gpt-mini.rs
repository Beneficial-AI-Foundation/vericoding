// <vc-preamble>
#![crate_name = "max_segment_sum"]

use vstd::prelude::*;

verus! {

spec fn sum(a: Seq<i32>, s: int, t: int) -> int
    decreases t - s,
{
    if s < 0 || s >= t || t > a.len() {
        0
    } else {
        a[t - 1] + sum(a, s, t - 1)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma expressing sum extension by one element */
proof fn sum_succ(a: Seq<i32>, s: int, t: int)
    requires
        0 <= s <= t,
        t + 1 <= a.len(),
    ensures
        sum(a, s, t + 1) == sum(a, s, t) + (a@[t as nat] as int),
    decreases
        t - s,
{
    assert(s < t + 1);
    assert(t + 1 <= a.len());
    assert(sum(a, s, t + 1) == (a@[t as nat] as int) + sum(a, s, t));
}

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn max_segment_sum(a: &Vec<i32>, s: usize, t: usize) -> (p: (usize, usize)) by (nonlinear_arith)
    ensures
        ({ let (i, j) = p; 0 <= i <= j <= a.len() }),
        ({ let (i, j) = p; forall|k: int, l: int| 0 <= k <= l <= a.len() ==> sum(a@, k, l) <= sum(a@, i as int, j as int) })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): exhaustive search using tracked spec-level sums */
    let n = a.len();
    let mut best_i: usize = 0;
    let mut best_j: usize = 0;
    tracked let mut best_sum: int = 0;

    let mut i: usize = 0;
    while i <= n
        invariant
            i <= n,
            best_sum == sum(a@, best_i as int, best_j as int),
            forall|k: int, l: int| 0 <= k <= l <= a.len() && k < i as int ==> sum(a@, k, l) <= best_sum,
        decreases
            a.len() - i
    {
        tracked let mut cur: int = 0;
        let mut j: usize = i;
        while j <= n
            invariant
                i <= j && j <= n,
                cur == sum(a@, i as int, j as int),
                best_sum == sum(a@, best_i as int, best_j as int),
                forall|k: int, l: int| 0 <= k <= l <= a.len() && (k < i as int || (k == i as int && l <= j as int)) ==> sum(a@, k, l) <= best_sum,
            decreases
                a.len() - j
        {
            if cur > best_sum {
                best_sum = cur;
                best_i = i;
                best_j = j;
            }
            if j == n {
                break;
            } else {
                proof {
                    sum_succ(a@, i as int, j as int);
                }
                cur = sum(a@, i as int, (j as int) + 1);
                j = j + 1;
            }
        }
        i = i + 1;
    }

    (best_i, best_j)
}
// </vc-code>

}
fn main() {}