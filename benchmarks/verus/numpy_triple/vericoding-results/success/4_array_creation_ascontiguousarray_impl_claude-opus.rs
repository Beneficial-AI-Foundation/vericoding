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
    /* code modified by LLM (iteration 2): Added decreases clause to while loop */
    if a.len() == 0 {
        let mut result = Vec::new();
        result.push(0.0f32);
        proof {
            assert(result.len() == 1);
            assert(result[0] == 0.0f32);
        }
        result
    } else {
        let mut result = Vec::new();
        let mut i = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                result.len() == i,
                forall|j: int| 0 <= j < i ==> #[trigger] result[j] == a[j],
            decreases a.len() - i
        {
            result.push(a[i]);
            i = i + 1;
        }
        proof {
            assert(result.len() == a.len());
            assert(forall|j: int| 0 <= j < a.len() ==> #[trigger] result[j] == a[j]);
        }
        result
    }
}
// </vc-code>

}
fn main() {}