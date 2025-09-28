// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn spacing(x: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < x@.len() ==> #[trigger] result@[i] as int > 0
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    for i in 0..x.len()
        invariant
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] as int > 0,
    {
        let val = if x[i] <= 0 { 1i8 } else { x[i] };
        result.push(val);
    }
    result
}
// </vc-code>


}
fn main() {}