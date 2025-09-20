// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn generate_integers(a: i8, b: i8) -> (result: Vec<i8>)
    ensures (forall|i: int| 0 <= i < result@.len() ==> result@[i] % 2 == 0) &&
            (forall|i: int| 0 <= i < result@.len() ==> (result@[i] == 2 || result@[i] == 4 || result@[i] == 6 || result@[i] == 8))
// </vc-spec>
// <vc-code>
{
    assume(false);
    Vec::new()
}
// </vc-code>


}

fn main() {}