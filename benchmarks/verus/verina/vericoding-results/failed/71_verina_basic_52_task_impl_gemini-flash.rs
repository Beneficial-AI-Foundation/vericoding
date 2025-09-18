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
{
    /* code modified by LLM (iteration 5): Fixed compilation error by removing `multiset_unit_proof_fn` as it's not needed. */
    let mut arr = a.clone();
    let n = arr.len();

    if n == 0 {
        return arr;
    }

    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i && i <= n,
            arr.len() == n,
            // Elements from n-i to n-1 are sorted
            forall|k: int, l: int| (n as int) - (i as int) <= k < l < (n as int) ==> arr@[k] <= arr@[l],
            a@.to_multiset() == arr@.to_multiset(),
            // Sorted elements are greater than unsorted elements
            forall|l: int, r: int|
                0 <= l < (n as int) - (i as int) && (n as int) - (i as int) <= r < (n as int) ==> arr@[l] <= arr@[r],
        decreases n - i
    {
        let mut j: usize = 0;
        while j < n - 1 - i
            invariant
                0 <= i && i < n,
                0 <= j && j <= (n as int) - 1 - (i as int),
                arr.len() == n,
                a@.to_multiset() == arr@.to_multiset(),
                // Elements from (n-i) to n-1 are sorted
                forall|k: int, l: int| (n as int) - (i as int) <= k < l < (n as int) ==> arr@[k] <= arr@[l],
                // Within the unsorted part, elements up to j are correctly placed relative to arr[j]
                forall|k: int| 0 <= k < (j as int) ==> arr@[k] <= arr@[j as int],
                // Elements in the sorted suffix are greater than elements in the unsorted prefix
                forall|l: int, r: int|
                    0 <= l < (n as int) - (i as int) && (n as int) - (i as int) <= r < (n as int) ==> arr@[l] <= arr@[r],
            decreases (n - 1 - i) - j
        {
            if arr[j] > arr[j + 1] {
                let temp = arr[j];
                arr.set(j, arr[j + 1]);
                arr.set(j + 1, temp);
             }
            j = j + 1;
        }
        i = i + 1;
    }
    arr
}
// </vc-code>

}
fn main() {}