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
    let mut result = Vec::new();
    let lower = if a <= b { a } else { b };
    let upper = if a <= b { b } else { a };
    
    if lower <= 2 && 2 <= upper {
        result.push(2);
    }
    if lower <= 4 && 4 <= upper {
        result.push(4);
    }
    if lower <= 6 && 6 <= upper {
        result.push(6);
    }
    if lower <= 8 && 8 <= upper {
        result.push(8);
    }
    
    result
}
// </vc-code>


}

fn main() {}