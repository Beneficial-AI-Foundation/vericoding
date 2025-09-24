// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: Seq<int>) -> bool {
    n >= 1 && n <= 90 &&
    a.len() == n &&
    (forall|i: int| 0 <= i < n ==> 1 <= #[trigger] a[i] <= 90) &&
    (forall|i: int, j: int| i + 1 == j && 0 <= i < n - 1 ==> #[trigger] a[i] < #[trigger] a[j])
}

spec fn find_cutoff(a: Seq<int>, index: int, cutoff: int) -> int
    decreases a.len() - index
    when 0 <= index <= a.len()
{
    if index >= a.len() {
        cutoff
    } else if a[index] > cutoff {
        cutoff
    } else {
        find_cutoff(a, index + 1, a[index] + 15)
    }
}

spec fn min(x: int, y: int) -> int {
    if x <= y { x } else { y }
}

spec fn valid_output(result: int, n: int, a: Seq<int>) -> bool {
    valid_input(n, a) ==>
    (1 <= result <= 90 &&
     result == min(90, find_cutoff(a, 0, 15)))
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, a@.map(|x| x as int))
    ensures valid_output(result as int, n as int, a@.map(|x| x as int))
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}