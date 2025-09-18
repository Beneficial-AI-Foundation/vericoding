// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no modifications needed */
// </vc-helpers>

// <vc-spec>
fn atleast_3d(arr: Vec<f32>) -> (result: Vec<Vec<Vec<f32>>>)
    ensures 
        result.len() == 1,
        forall|j: int| 0 <= j < 1 ==> #[trigger] result[j].len() == arr.len(),
        forall|j: int, k: int| 0 <= j < 1 && 0 <= k < arr.len() ==> #[trigger] result[j][k].len() == 1,
        forall|i: int| 0 <= i < arr.len() ==> {
            let outer = &result[0];
            let middle = &outer[i];
            let value = middle[0];
            value == #[trigger] arr[i]
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type annotation for inner vector in vec new */
    let mut result: Vec<Vec<Vec<f32>>> = Vec::new();
    let mut inner: Vec<Vec<f32>> = Vec::new();
    for i in 0..arr.len()
        invariant
            0 <= i <= arr.len(),
            inner.len() == i,
            forall |k: int| 0 <= k < i ==> inner[k].len() == 1,
            forall |k: int| 0 <= k < i ==> inner[k][0] == arr[k]
    {
        let mut nested = Vec::new();
        nested.push(arr[i]);
        inner.push(nested);
    }
    result.push(inner);
    proof {
        assert(result.len() == 1);
        assert(result[0].len() == arr.len());
        assert forall |k: int| 0 <= k < arr.len() implies result[0][k].len() == 1 by {
            // from invariant
        };
        assert forall |i: int| 0 <= i < arr.len() implies result[0][i][0] == arr[i] by {
            // from invariant
        };
    }
    result
}
// </vc-code>

}
fn main() {}