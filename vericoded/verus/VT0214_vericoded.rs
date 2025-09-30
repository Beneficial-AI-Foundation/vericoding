// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_unit_eq()
    ensures
        () == (),
{
}

// </vc-helpers>

// <vc-spec>
fn save(file: String, arr: Vec<f32>, allow_pickle: bool) -> (result: ())
    ensures result == (),
// </vc-spec>
// <vc-code>
{
    proof { lemma_unit_eq(); }
    let _ = file;
    let _ = arr;
    let _ = allow_pickle;
    ()
}
// </vc-code>

}
fn main() {}