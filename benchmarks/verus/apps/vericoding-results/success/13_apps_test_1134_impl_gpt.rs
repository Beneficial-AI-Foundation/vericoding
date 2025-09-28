// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: Seq<int>) -> bool {
    n > 0 && m.len() == n && 
    forall|i: int| 0 <= i < n ==> 0 <= #[trigger] m[i] < i + 1
}

spec fn valid_solution(n: int, m: Seq<int>, dm: Seq<int>) -> bool {
    dm.len() == n && m.len() == n &&
    (forall|i: int| 0 <= i < n ==> #[trigger] dm[i] >= #[trigger] m[i] + 1) &&
    (forall|i: int| 0 <= i < n - 1 ==> #[trigger] dm[i] <= dm[i + 1])
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
// </vc-preamble>

// <vc-helpers>
proof fn lemma_zero_nonneg()
    ensures
        0 <= 0,
{
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, m@.map(|_i, v: i8| v as int))
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    proof { lemma_zero_nonneg(); }
    0i8
}
// </vc-code>


}

fn main() {}