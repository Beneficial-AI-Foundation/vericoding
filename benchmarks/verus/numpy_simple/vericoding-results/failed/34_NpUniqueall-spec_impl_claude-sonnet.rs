// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn unique_all(arr: Vec<i8>) -> (ret: Vec<i8>)
    ensures
        ret.len() <= arr.len(),
        forall|i: int| 0 <= i < arr@.len() ==> exists|j: int| 0 <= j < ret@.len() && ret@[j] == #[trigger] arr@[i],
        forall|i: int, j: int| 0 <= i < ret@.len() && 0 <= j < i ==> ret@[i] != ret@[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added trigger annotations to fix quantifier inference */
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            result.len() <= i,
            forall|k: int| 0 <= k < i ==> exists|j: int| 0 <= j < result@.len() && result@[j] == #[trigger] arr@[k],
            forall|x: int, y: int| 0 <= x < result@.len() && 0 <= y < x ==> #[trigger] result@[x] != #[trigger] result@[y],
        decreases arr.len() - i
    {
        let mut found = false;
        let mut j: usize = 0;
        while j < result.len()
            invariant
                j <= result.len(),
                i < arr.len(),
                found <==> exists|k: int| 0 <= k < j && result@[k] == arr@[i as int],
            decreases result.len() - j
        {
            if result[j] == arr[i] {
                found = true;
                break;
            }
            j += 1;
        }
        if !found {
            result.push(arr[i]);
            proof {
                assert(forall|k: int| 0 <= k < (i + 1) ==> exists|l: int| 0 <= l < result@.len() && result@[l] == #[trigger] arr@[k]);
                assert(forall|x: int, y: int| 0 <= x < result@.len() && 0 <= y < x ==> #[trigger] result@[x] != #[trigger] result@[y]);
            }
        }
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}