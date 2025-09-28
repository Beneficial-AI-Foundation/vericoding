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
    let n = x.len();
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] as int == 1,
        decreases n - i
    {
        result.push(1i8);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}