// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn sorted_implies_unique(arr: Seq<i32>) -> (result: bool)
    ensures
        result == (forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] != arr[j]),
{
    if arr.len() == 0 {
        true
    } else {
        let sub = arr.subrange(1, arr.len() as int);
        let sub_unique = sorted_implies_unique(sub);
        &&& sub_unique
        &&& forall|j: int| 1 <= j < arr.len() ==> arr[0] != arr[j]
    }
}

/* helper modified by LLM (iteration 5): Fixed old_vec to avoid mutable reference */
proof fn old_vec(vec: &Vec<i32>) -> (result: Seq<i32>)
    ensures result == old(vec)@,
{
    vec@
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
    /* code modified by LLM (iteration 5): Fixed swap operation to avoid &mut complexity */
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    
    while i < arr.len()
        invariant
            result.len() <= i,
            forall|k: int| 0 <= k < result.len() - 1 ==> #[trigger] result[k] <= result[k + 1],
            forall|x: i32| result@.contains(x) ==> arr@.contains(x),
            forall|j: int| 0 <= j < i ==> arr@.contains(arr[j]) && result@.contains(arr[j]),
    {
        if !result.contains(&arr[i]) {
            let old_len = result.len();
            result.push(arr[i]);
            let mut j = result.len() - 1;
            while j > 0 && result[j - 1] > result[j]
                invariant
                    result.len() == old_len + 1,
                    forall|k: int| 0 <= k < result.len() - 1 ==> #[trigger] result[k] <= result[k + 1],
            {
                let temp = result[j - 1];
                result[j - 1] = result[j];
                result[j] = temp;
                j -= 1;
            }
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}