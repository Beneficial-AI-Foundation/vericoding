// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
spec fn is_nonneg(x: int) -> bool { x >= 0 }
proof fn lemma_unit() ensures () == () { }
// </vc-helpers>

// <vc-spec>
fn numpy_tofile(arr: Vec<f32>, filename: String) -> (result: ())
    requires true,
    ensures result == ()
// </vc-spec>
// <vc-code>
{
    let _ = arr;
    let _ = filename;
    ()
}
// </vc-code>

}
fn main() {}