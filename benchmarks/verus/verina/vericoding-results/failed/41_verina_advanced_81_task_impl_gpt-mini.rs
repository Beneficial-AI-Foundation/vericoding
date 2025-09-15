// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): convert Vec<i32> to Seq<i32> */
spec fn vec_to_seq(v: &Vec<i32>) -> Seq<i32> { v@ }
// </vc-helpers>

// <vc-spec>
fn unique_sorted(arr: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() <= arr.len(),
        forall|i: int| 0 <= i < result.len() - 1 ==> #[trigger] result[i] <= result[i + 1],
        forall|x: i32| arr@.contains(x) <==> result@.contains(x),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build unique sorted Vec while maintaining invariants */
    let mut result: Vec<i32> = Vec::new();
    let mut i: int = 0;
    while i < arr.len()
        invariant 0 <= i && i <= arr.len()
        invariant result.len() <= arr.len()
        invariant forall|y: i32| result@.contains(y) <==> (exists|k: int| 0 <= k < i && arr@[k] == y)
        invariant forall|p: int, q: int| 0 <= p < result.len() && 0 <= q < result.len() && result[p] == result[q] ==> p == q
        invariant forall|t: int| 0 <= t < result.len() - 1 ==> result[t] < result[t + 1]
        decreases arr.len() - i
    {
        let x: i32 = arr[i];

        let mut found: bool = false;
        let mut j: int = 0;
        while j < result.len()
            invariant 0 <= j && j <= result.len()
            invariant result.len() <= arr.len()
            invariant forall|y: i32| result@.contains(y) <==> (exists|k: int| 0 <= k < i && arr@[k] == y)
            decreases result.len() - j
        {
            if result[j] == x {
                found = true;
                break;
            }
            j += 1;
        }

        if !found {
            let mut k: int = 0;
            while k < result.len()
                invariant 0 <= k && k <= result.len()
                invariant result.len() <= arr.len()
                invariant forall|y: i32| result@.contains(y) <==> (exists|t: int| 0 <= t < i && arr@[t] == y)
                decreases result.len() - k
            {
                if result[k] >= x {
                    break;
                }
                k += 1;
            }
            result.insert(k, x);

            proof {
                assert(forall|y: i32| result@.contains(y) <==> (exists|t: int| 0 <= t < i + 1 && arr@[t] == y));
            }
        }

        i += 1;
    }

    result
}
// </vc-code>

}
fn main() {}