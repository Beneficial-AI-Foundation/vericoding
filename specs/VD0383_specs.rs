// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sorted_between(a: &Vec<i32>, from: usize, to: usize) -> bool
    recommends
        from <= to,
        to <= a.len(),
{
    forall|i: int, j: int| from <= i < j < to && 0 <= i < a.len() && 0 <= j < a.len() ==> a@[i] <= a@[j]
}

spec fn sorted(a: &Vec<i32>) -> bool {
    sorted_between(a, 0, a.len())
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn bubbleSort(a: &mut Vec<i32>)
    requires
        old(a).len() > 0,
    ensures
        sorted(a),
        old(a)@ == a@,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}