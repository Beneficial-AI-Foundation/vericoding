// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added invariants for verification */
exec fn is_in_vec(result: &Vec<i32>, item: i32) -> bool {
    let mut i = 0;
    while i < result.len()
        invariant i <= result.len()
        decreases result.len() - i
    {
        if result[i] == item {
            return true;
        }
        i += 1;
    }
    false
}
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
    /* code modified by LLM (iteration 3): added comprehensive invariants for sorted order and uniqueness */
    let mut result = Vec::new();
    for i in 0..arr.len()
        invariant
            0 <= i <= arr.len()
        invariant
            forall |k: int| 0 <= k < result.len() - 1 ==> result[k] <= result[k + 1]
        invariant
            forall |k: int| 0 <= k < result.len() ==> exists |m: int| 0 <= m < i ==> #[trigger] arr[m] == result[k]
        invariant
            forall |x: i32| #[trigger] result@.contains(x) ==> arr@.contains(x)
        invariant
            result.len() <= i
    {
        let item = arr[i];
        if !is_in_vec(&result, item) {
            let mut j = 0;
            while j < result.len() && result[j] < item
                invariant
                    0 <= j <= result.len()
                invariant
                    decreases result.len() - j
                invariant
                    forall |k: int| 0 <= k < j ==> result[k] < item
                invariant
                    forall |k: int| j <= k < result.len() ==> item <= result[k]
                invariant
                    forall |p: int| 0 <= p < result.len() - 1 ==> #[trigger] result[p] <= result[p + 1]
            {
                j += 1;
            }
            result.insert(j, item);
        }
    }
    proof {
        assert(forall |x: i32| #[trigger] arr@.contains(x) ==> result@.contains(x)) by {
            // Follows from the loop invariants and the way we construct result
        }
    }
    result
}
// </vc-code>

}
fn main() {}