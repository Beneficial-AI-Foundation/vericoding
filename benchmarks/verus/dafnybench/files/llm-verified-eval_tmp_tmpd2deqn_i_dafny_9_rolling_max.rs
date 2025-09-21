// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn isMax(m: int, numbers: Seq<int>) -> bool {
    numbers.contains(m) &&
    forall|i: int| 0 <= i < numbers.len() ==> numbers[i] <= m
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn rolling_max(numbers: Vec<i8>) -> (result: Vec<i8>)
    requires
        numbers.len() > 0,
    ensures
        result.len() == numbers.len(),
        forall|i: int| 0 < i < result.len() ==> isMax(result[i] as int, numbers@.map(|_index, x| x as int).subrange(0, i + 1)),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}