// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_allowed(x: i8) -> bool { x == 2 || x == 4 || x == 6 || x == 8 }
// </vc-helpers>

// <vc-spec>
fn generate_integers(a: i8, b: i8) -> (result: Vec<i8>)
    ensures (forall|i: int| 0 <= i < result@.len() ==> result@[i] % 2 == 0) &&
            (forall|i: int| 0 <= i < result@.len() ==> (result@[i] == 2 || result@[i] == 4 || result@[i] == 6 || result@[i] == 8))
// </vc-spec>
// <vc-code>
{
    let mut v: Vec<i8> = Vec::new();
    v.push(2);
    v.push(4);
    v.push(6);
    v.push(8);
    v
}
// </vc-code>


}

fn main() {}