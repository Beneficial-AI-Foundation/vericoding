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

proof fn min_proof_lemma(a: int, b: int)
    ensures
        a <= b ==> min_spec(a, b) == a,
        a > b ==> min_spec(a, b) == b,
{
}
// </vc-helpers>

// <vc-spec>
fn my_min(x: i32, y: i32) -> (result: i32)
    ensures
        (x <= y ==> result == x) && (x > y ==> result == y),
// </vc-spec>
// <vc-code>
{
    let result = if x <= y { x } else { y };
    proof {
        min_proof_lemma(x as int, y as int);
    }
    result
}
// </vc-code>

}
fn main() {}