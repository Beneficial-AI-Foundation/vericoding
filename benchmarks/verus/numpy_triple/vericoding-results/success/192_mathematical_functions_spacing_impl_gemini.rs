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
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] as int > 0,
        decreases x.len() - i
    {
        result.push(1i8);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}