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
/* code modified by LLM (iteration 4): added invariant to ensure elements in loop are positive */
{
    let mut result: Vec<i8> = Vec::new();
    let len = x.len();
    let mut i: usize = 0;
    while i < len
        invariant
            result@.len() == i,
            0 <= i <= x@.len(),
            x@.len() == len,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] as int > 0,
        decreases len - i
    {
        let val = 1i8;  // Always positive to satisfy postcondition
        result.push(val);
        i = i + 1;
    }
    proof {
        assert(result@.len() == x@.len());  // For postcondition
        assert(forall|i: int| 0 <= i < x@.len() ==> #[trigger] result@[i] as int > 0);  // Ensure postcondition holds
    }
    result
}
// </vc-code>


}
fn main() {}