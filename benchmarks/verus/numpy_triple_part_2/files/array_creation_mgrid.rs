// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn mgrid(start: i32, stop: i32, step: i32, n: usize) -> (result: Vec<i32>)
    requires
        step > 0,
        start < stop,
        n == ((stop - start) as int / step as int) as usize,
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] == start + (i as i32) * step,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] < stop,
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