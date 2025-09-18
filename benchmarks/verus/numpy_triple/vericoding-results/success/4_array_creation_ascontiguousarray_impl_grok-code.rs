// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn ascontiguousarray(a: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() >= 1,
        a.len() > 0 ==> result.len() == a.len(),
        a.len() == 0 ==> result.len() == 1,
        a.len() > 0 ==> forall|i: int| 0 <= i < a.len() ==> #[trigger] result[i] == a[i],
        a.len() == 0 ==> result.len() == 1 && result[0] == 0.0f32,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Improved loop invariants using result.len() and explicit bounds to fix postcondition for length equality */
    if a.len() == 0 {
        let mut result = Vec::new();
        result.push(0.0f32);
        result
    } else {
        let mut result = Vec::new();
        let mut i = 0;
        while i < a.len()
            invariant
                result.len() as int == i as int,
                forall|j: int| 0 <= j < i as int ==> #[trigger] result@[j] == a@[j],
                i as int <= a.len() as int
            decreases a.len() as int - (i as int)
        {
            result.push(a[i]);
            i += 1;
        }
        result
    }
}
// </vc-code>

}
fn main() {}