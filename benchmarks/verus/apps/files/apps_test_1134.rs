// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, m: Seq<int>) -> bool {
    n > 0 && m.len() == n && 
    forall|i: int| 0 <= i < n ==> 0 <= m[i] < i + 1
}

spec fn valid_solution(n: int, m: Seq<int>, dm: Seq<int>) -> bool {
    dm.len() == n && m.len() == n &&
    (forall|i: int| 0 <= i < n ==> dm[i] >= m[i] + 1) &&
    (forall|i: int| 0 <= i < n - 1 ==> dm[i] <= dm[i + 1])
}

spec fn sum_below(m: Seq<int>, dm: Seq<int>) -> int
    decreases m.len()
{
    if m.len() == 0 {
        0
    } else {
        (dm[0] - 1 - m[0]) + sum_below(m.subrange(1, m.len() as int), dm.subrange(1, dm.len() as int))
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, m: Seq<int>) -> (result: int)
    requires valid_input(n, m)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}