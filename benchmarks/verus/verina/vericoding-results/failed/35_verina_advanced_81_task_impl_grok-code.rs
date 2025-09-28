// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added ensures to insertion_sort for verification and fixed typing issues with ranges and old values in invariants. */
spec fn is_sorted(s: Seq<i32>) -> bool {
    forall|i: int| 0 <= i < s.len() - 1 ==> #[trigger] s[i] <= s[i + 1]
}

fn insertion_sort(vec: &mut Vec<i32>)
    ensures
        vec@.len() == old(vec@).len(),
        forall|x: i32| old(vec@).contains(x) <==> vec@.contains(x),
        is_sorted(vec@),
{
    let initial: Seq<i32> = vec@;
    let n = vec.len();
    if n <= 1 { return; }
    let mut i = 1;
    while i < n
        invariant
            1 <= i <= n,
            vec@.len() == n as int,
            is_sorted(vec@[(0int)..(i as int)]),
            forall|k: int| i <= k < n ==> vec@[k] == initial[k],
            forall|x: i32| old(vec@).contains(x) <==> vec@.contains(x),
    {
        let key = vec[i];
        let mut j = i;
        while j > 0 && vec[j-1] > key
            invariant
                0 <= j <= i,
        {
            vec[j] = vec[j-1];
            j = j - 1;
        }
        vec[j] = key;
        i = i + 1;
    }
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
/* code modified by LLM (iteration 2): Implemented loop to remove duplicates and then sort the result. */
    let mut result = Vec::new();
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            result.len() <= i,
            forall|k: int| 0 <= k < result.len() ==> arr@.contains(result@[k]),
    {
        let x = arr[i];
        if !result.contains(&x) {
            result.push(x);
        }
        i = i + 1;
    }
    insertion_sort(&mut result);
    result
}
// </vc-code>

}
fn main() {}