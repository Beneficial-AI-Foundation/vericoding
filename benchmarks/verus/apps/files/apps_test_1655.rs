// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: Seq<int>) -> bool {
    n >= 1 && a.len() == n && forall|i: int| 0 <= i < n ==> a[i] >= 0
}

spec fn count_survivors(n: int, a: Seq<int>) -> int {
    count_survivors_from(n, a, 0, n)
}

spec fn count_survivors_from(n: int, a: Seq<int>, start: int, left: int) -> int
    decreases n - start
{
    if start >= n {
        0
    } else {
        let i = n - 1 - start;
        let survives: int = if i < left { 1 } else { 0 };
        let new_left: int = if i - a[i] < left { i - a[i] } else { left };
        survives + count_survivors_from(n, a, start + 1, new_left)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a@.map_values(|x: i8| x as int))
    ensures result >= 0 && result <= n && result as int == count_survivors(n as int, a@.map_values(|x: i8| x as int))
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}