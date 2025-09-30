// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn choose_odd()
// </vc-spec>
// <vc-code>
{
}

// </vc-code>

}
fn main() {}