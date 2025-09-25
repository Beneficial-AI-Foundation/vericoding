// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn unique(arr: Vec<i8>) -> (result: Vec<i8>)
    ensures

        forall|i: int, j: int| 0 <= i < j < result@.len() ==> #[trigger] result@[i] < #[trigger] result@[j],

        forall|i: int| 0 <= i < result@.len() ==> exists|j: int| 0 <= j < arr@.len() && #[trigger] result@[i] == #[trigger] arr@[j],

        forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < result@.len() && i != j ==> #[trigger] result@[i] != #[trigger] result@[j],

        forall|i: int| 0 <= i < arr@.len() ==> exists|j: int| 0 <= j < result@.len() && #[trigger] arr@[i] == #[trigger] result@[j],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}