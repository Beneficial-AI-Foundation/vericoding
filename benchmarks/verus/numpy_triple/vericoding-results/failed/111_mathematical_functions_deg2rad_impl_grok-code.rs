// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn deg2rad(degrees: Vec<i8>) -> (radians: Vec<i8>)
    ensures 
        radians.len() == degrees.len(),
        forall|i: int| 0 <= i < degrees.len() ==> #[trigger] radians@[i] as int == degrees@[i] as int * 314 / 18000
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let len = degrees.len();
    for i in 0..len
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] as int == degrees@[j] as int * 314 / 18000,
    {
        let deg = degrees[i] as int;
        let rad = (deg * 314) / 18000;
        result.push(rad as i8);
    }
    result
}
// </vc-code>


}
fn main() {}