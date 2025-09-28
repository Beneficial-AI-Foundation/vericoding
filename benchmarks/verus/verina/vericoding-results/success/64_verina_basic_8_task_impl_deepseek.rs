// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn min_spec(a: int, b: int) -> int {
    if a <= b {
        a
    } else {
        b
    }
}

proof fn min_lemma(a: int, b: int) -> (result: int)
    ensures
        result <= a && result <= b,
        result == a || result == b,
{
    if a <= b {
        a
    } else {
        b
    }
}
// </vc-helpers>

// <vc-spec>
fn my_min(a: i32, b: i32) -> (result: i32)
    ensures
        result <= a && result <= b,
        result == a || result == b,
// </vc-spec>
// <vc-code>
{
    let result = if a <= b { a } else { b };
    result
}
// </vc-code>

}
fn main() {}