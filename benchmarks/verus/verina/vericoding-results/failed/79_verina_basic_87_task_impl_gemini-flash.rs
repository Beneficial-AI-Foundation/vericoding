// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers. */
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i <= j < result.len() ==> result[i] <= result[j],
        result@ =~= a@,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Added decreases clauses for both while loops. */
{
    let mut arr = a.clone();
    let n = arr.len();

    if n == 0 {
        return arr;
    }

    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            arr.len() == n,
            forall|k: int, l: int| 0 <= k <= l < i ==> arr[k] <= arr[l],
        decreases (n - i)
    {
        let mut min_idx = i;
        let mut j = i + 1;
        while j < n
            invariant
                i < j <= n,
                min_idx < n,
                arr.len() == n,
                forall|k: int| i <= k < j ==> arr[min_idx as int] <= arr[k as int],
            decreases (n - j)
        {
            if arr[j] < arr[min_idx] {
                min_idx = j;
            }
            j = j + 1;
        }

        if min_idx != i {
            let temp = arr[i];
            arr[i] = arr[min_idx];
            arr[min_idx] = temp;
        }
        i = i + 1;
    }
    arr
}
// </vc-code>

}
fn main() {}