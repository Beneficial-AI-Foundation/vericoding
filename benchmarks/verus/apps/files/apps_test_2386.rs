// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, a: Seq<int>) -> bool {
    n >= 1 && a.len() == n && forall|i: int| 0 <= i < a.len() ==> a[i] >= 1
}

spec fn transform(a: Seq<int>) -> Seq<int> {
    Seq::new(a.len(), |i: int| a[i] - (i + 1))
}

spec fn sum_abs_diffs(a: Seq<int>, target: int) -> int
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        abs_int(a[0] - target) + sum_abs_diffs(a.subrange(1, a.len() as int), target)
    }
}

spec fn median_of(a: Seq<int>) -> int {
    let sorted = sorted_seq(a);
    if sorted.len() == 0 {
        0
    } else if sorted.len() % 2 == 1 {
        sorted[sorted.len() as int / 2]
    } else if sorted.len() == 2 {
        (sorted[0] + sorted[1]) / 2
    } else {
        (sorted[sorted.len() as int / 2 - 1] + sorted[sorted.len() as int / 2]) / 2
    }
}

spec fn sorted_seq(a: Seq<int>) -> Seq<int> {
    a
}

spec fn abs_int(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, a@.map(|i: int, x: i8| x as int)),
    ensures 
        result >= 0,
        result as int == sum_abs_diffs(transform(a@.map(|i: int, x: i8| x as int)), median_of(transform(a@.map(|i: int, x: i8| x as int)))),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}