// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_trivial()
    ensures
        true,
{
}

// </vc-helpers>

// <vc-spec>
fn numpy_tofile(arr: Vec<f32>, filename: String) -> (result: ())
    requires true,
    ensures result == ()
// </vc-spec>
// <vc-code>
{
    proof { lemma_trivial(); }
    ()
}
// </vc-code>

}
fn main() {}