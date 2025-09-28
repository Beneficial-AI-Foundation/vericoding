// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn bubble_sort(a: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        a@.to_multiset() == result@.to_multiset(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): added trigger for quantifier in inner loop invariant */
{
    let n = a.len();
    let mut arr = a.clone();
    let mut i = 0;
    while i < n
        invariant
            n == a.len(),
            arr.len() == n,
            arr@.to_multiset() == a@.to_multiset(),
            forall|k: int, l: int| n - i <= k < l < n ==> arr[k] <= arr[l],
            forall|k: int, l: int| 0 <= k < n - i && n - i <= l < n ==> arr[k] <= arr[l],
        decreases n - i
    {
        let mut j = 0;
        while j < n - i - 1
            invariant
                j <= n - i - 1,
                arr.len() == n,
                arr@.to_multiset() == a@.to_multiset(),
                forall|k: int, l: int| n - i <= k < l < n ==> arr[k] <= arr[l],
                forall|k: int, l: int| 0 <= k < n - i && n - i <= l < n ==> arr[k] <= arr[l],
                forall|k: int| 0 <= k <= j ==> (#[trigger] arr[k]) <= arr[j+1],
            decreases n - i - 1 - j
        {
            if arr[j] > arr[j+1] {
                let temp = arr[j];
                arr[j] = arr[j+1];
                arr[j+1] = temp;
            }
            j += 1;
        }
        i += 1;
    }
    arr
}
// </vc-code>

}
fn main() {}