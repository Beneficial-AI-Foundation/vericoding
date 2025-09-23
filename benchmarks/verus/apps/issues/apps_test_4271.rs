// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: Seq<int>, b: Seq<int>, c: Seq<int>) -> bool {
    n >= 1 &&
    a.len() == n &&
    b.len() == n &&
    c.len() == n - 1 &&
    (forall|i: int| 0 <= i < n ==> 1 <= #[trigger] a[i] <= n) &&
    (forall|i: int, j: int| 0 <= i < j < n ==> #[trigger] a[i] != #[trigger] a[j])
}

spec fn sum_satisfaction(a: Seq<int>, b: Seq<int>, c: Seq<int>, n: int) -> int
    recommends
        n >= 1,
        a.len() == n,
        b.len() == n,
        c.len() == n - 1,
        forall|i: int| 0 <= i < n ==> 1 <= #[trigger] a[i] <= n
{
    sum_satisfaction_up_to(a, b, c, n)
}

spec fn sum_satisfaction_up_to(a: Seq<int>, b: Seq<int>, c: Seq<int>, k: int) -> int
    recommends
        0 <= k <= a.len(),
        b.len() == a.len(),
        c.len() == a.len() - 1,
        forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= a.len()
    decreases k
{
    if k <= 0 {
        0
    } else {
        let prev_sum = sum_satisfaction_up_to(a, b, c, k - 1);
        let base_contrib = b[a[k - 1] - 1];
        let bonus_contrib = if k > 1 && a[k - 1] == a[k - 2] + 1 {
            c[a[k - 1] - 2]
        } else {
            0
        };
        prev_sum + base_contrib + bonus_contrib
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>, b: Vec<i8>, c: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a@.map(|x| x as int), b@.map(|x| x as int), c@.map(|x| x as int))
    ensures result as int == sum_satisfaction(a@.map(|x| x as int), b@.map(|x| x as int), c@.map(|x| x as int), n as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}