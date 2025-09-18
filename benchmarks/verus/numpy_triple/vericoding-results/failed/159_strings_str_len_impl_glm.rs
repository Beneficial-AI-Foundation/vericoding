// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn str_len(a: Vec<String>) -> (result: Vec<nat>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            &&& result[i] == a[i]@.len()
            &&& result[i] >= 0
            &&& (a[i]@.len() == 0 <==> a[i]@ == Seq::<char>::empty())
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): fixed type issues with int and usize, use sequence views for length */
{
    let mut result = Vec::new();
    let mut i: int = 0 as int;
    while i < a@.len()
        invariant
            0 <= i <= a@.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] == a@[j]@.len(),
        decreases a@.len() - i,
    {
        let idx = i as usize;
        result.push(a[idx]@.len());
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}