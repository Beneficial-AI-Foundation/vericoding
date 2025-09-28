// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn true_lemma() {
    // This lemma has no body as it's just proving 'true' which is trivial.
    // The ensures clause of true_() directly states its properties.
}
// </vc-helpers>

// <vc-spec>
fn true_() -> (result: bool)
    ensures 
        result == true,
        !result == false
// </vc-spec>
// <vc-code>
{
    true
}
// </vc-code>

}
fn main() {}