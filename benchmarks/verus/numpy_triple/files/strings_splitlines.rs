// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn splitlines(a: Vec<String>, keepends: bool) -> (result: Vec<Vec<String>>)
    requires a@.len() > 0,
    ensures 
        result@.len() == a@.len(),
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] result@[i]@.len() >= 1
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}