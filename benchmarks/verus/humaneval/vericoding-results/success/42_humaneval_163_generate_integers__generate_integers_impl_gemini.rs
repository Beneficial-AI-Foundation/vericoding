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
    /* code modified by LLM (iteration 2): fixed compilation error and implemented correct logic without a complex loop */
    let mut result: Vec<i8> = Vec::new();

    let min_val = if a < b { a } else { b };
    let max_val = if a > b { a } else { b };

    if min_val <= 2 && 2 <= max_val {
        result.push(2);
    }
    if min_val <= 4 && 4 <= max_val {
        result.push(4);
    }
    if min_val <= 6 && 6 <= max_val {
        result.push(6);
    }
    if min_val <= 8 && 8 <= max_val {
        result.push(8);
    }
    
    result
}
// </vc-code>


}

fn main() {}