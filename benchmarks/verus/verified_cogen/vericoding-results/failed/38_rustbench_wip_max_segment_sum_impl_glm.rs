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
/* helper modified by LLM (iteration 2): added complete proof implementations for sum lemmas */
proof fn sum_empty(a: Seq<i32>, s: int)
    ensures sum(a, s, s) == 0
{
    reveal(sum);
}

proof fn sum_single(a: Seq<i32>, s: int)
    requires 0 <= s < a.len()
    ensures sum(a, s, s + 1) == a[s]
{
    reveal(sum);
}

proof fn sum_concat(a: Seq<i32>, s: int, m: int, t: int)
    requires 0 <= s <= m <= t <= a.len()
    ensures sum(a, s, t) == sum(a, s, m) + sum(a, m, t)
{
    if s == m || m == t {
        reveal(sum);
    } else {
        reveal(sum);
        sum_concat(a, s, m, t - 1);
    }
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
/* code modified by LLM (iteration 5): fixed loop invariant syntax by enclosing invariants in a single block per loop */
{
    let mut max_sum = 0;
    let mut max_start: usize = s;
    let mut max_end: usize = s;
    
    for i in s..t
        invariant {
            s <= i;
            i <= t;
            0 <= max_start;
            max_start <= max_end;
            max_end <= a.len();
            forall|k: int, l: int| 0 <= k <= l <= a.len() && (k < s as int || l > i as int) ==> sum(a@, k, l) <= sum(a@, max_start as int, max_end as int);
            forall|k: int, l: int| s as int <= k <= l <= i as int ==> sum(a@, k, l) <= sum(a@, max_start as int, max_end as int);
        }
    {
        let mut current_sum = 0;
        for j in i..t
            invariant {
                i <= j;
                j <= t;
                current_sum == sum(a@, i as int, j as int);
                forall|k: int| i as int <= k < j as int ==> max_sum >= sum(a@, i as int, k as int);
            }
        {
            current_sum = current_sum + a[j];
            if current_sum > max_sum {
                max_sum = current_sum;
                max_start = i;
                max_end = j + 1;
            }
        }
    }
    
    (max_start, max_end)
}
// </vc-code>

}
fn main() {}