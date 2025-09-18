// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
spec fn is_nonneg(x: int) -> bool { x >= 0 }
// </vc-helpers>

// <vc-spec>
fn inf() -> (result: f32)
// </vc-spec>
// <vc-code>
{
    0.0f32
}
// </vc-code>

}
fn main() {}