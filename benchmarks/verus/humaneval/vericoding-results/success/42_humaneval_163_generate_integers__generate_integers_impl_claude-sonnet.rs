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
    /* code modified by LLM (iteration 2): fixed type annotation for Vec */
    let mut result: Vec<i8> = Vec::new();
    let mut i = 2i8;
    while i <= 8
        invariant
            forall|j: int| 0 <= j < result@.len() ==> result@[j] % 2 == 0,
            forall|j: int| 0 <= j < result@.len() ==> (result@[j] == 2 || result@[j] == 4 || result@[j] == 6 || result@[j] == 8),
            i == 2 + 2 * result@.len(),
            i <= 10,
        decreases 10 - i
    {
        result.push(i);
        i = i + 2;
    }
    result
}
// </vc-code>


}

fn main() {}