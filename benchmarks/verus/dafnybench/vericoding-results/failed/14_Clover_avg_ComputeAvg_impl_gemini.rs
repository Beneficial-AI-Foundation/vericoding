// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn compute_avg(a: int, b: int) -> (avg: int)
    ensures avg == (a + b) / 2
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): an `fn` with `int` parameters is a ghost function, and its body must be ghost code. The previous `as int` cast caused a compilation error. Simply using the literal `2` allows for correct type inference. */
    (a + b) / 2
}
// </vc-code>

}
fn main() {}