// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn sorted_even(a: Vec<i8>) -> (sorted: Vec<i8>)
    requires 
        a@.len() > 0
    ensures 
        sorted@.len() == a@.len(),
        forall|i: int, j: int| 0 <= i < j && 2 * i < sorted@.len() && 2 * j < sorted@.len() ==> #[trigger] sorted@[2 * i] <= #[trigger] sorted@[2 * j],
        forall|i: int| 0 <= i < a@.len() && i % 2 == 1 ==> #[trigger] sorted@[i] == #[trigger] a@[i],
        a@.to_multiset() == sorted@.to_multiset()
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): Replace loop implementation with extraction of even values, sorting, and reassignment to ensure verification */
    let mut sorted = a;
    let len = sorted.len();
    let mut even_vals = Vec::new();
    let mut i: usize = 0;
    while i < len 
        invariant
            0 <= i,
        decreases len - i,
    {
        if i % 2 == 0 {
            even_vals.push(sorted[i]);
        }
        i += 1;
    }
    even_vals.sort();
    let mut idx = 0;
    i = 0;
    while i < len 
        invariant
            0 <= i,
            0 <= idx <= even_vals.len(),
        decreases len - i,
    {
        if i % 2 == 0 {
            sorted[i] = even_vals[idx];
            idx += 1;
        }
        i += 1;
    }
    sorted
}
// </vc-code>


}

fn main() {}