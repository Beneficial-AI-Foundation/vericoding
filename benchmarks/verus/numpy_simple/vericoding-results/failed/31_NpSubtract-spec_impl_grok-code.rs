// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn subtract(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result@[i] == a@[i] - b@[i],
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): fixed compilation by replacing index_get with index */
let mut result = Vec::with_capacity(a.len());
let mut i = 0;
while i < a.len()
    invariant
        result.len() == i,
        a.len() == b.len(),
        forall|j: int| #[trigger] (0 <= j < i) ==> result@[j] == a@[j] - b@[j],
    decreases a.len() - i
{
    result.push(*a.index(i) - *b.index(i));
    i += 1;
}
result
}
// </vc-code>


}
fn main() {}