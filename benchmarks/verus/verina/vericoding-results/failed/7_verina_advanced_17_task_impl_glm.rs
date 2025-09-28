// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_sorted_range(arr: Vec<i32>, start: int, end: int) -> bool {
        forall|i: int, j: int| start <= i < j < end ==> arr[i] <= arr[j]
    }
// </vc-helpers>

// <vc-spec>
fn insertion_sort(l: Vec<i32>) -> (result: Vec<i32>)
    ensures

        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],

        result@.to_multiset() == l@.to_multiset(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added decreases clause for inner while loop */
{
        let mut arr = l;
        let ghost orig_multiset = arr@.to_multiset();

        for i in 1..arr.len()
            invariant
                is_sorted_range(arr, 0, i as int),
                arr@.to_multiset() == orig_multiset,
        {
            let key = arr[i];
            let mut j = i;
            while j > 0 && key < arr[j-1]
                invariant
                    0 < j <= i,
                    is_sorted_range(arr, 0, j as int),
                    arr@.to_multiset() == orig_multiset,
                decreases j
            {
                arr[j] = arr[j-1];
                j -= 1;
            }
            arr[j] = key;

            proof {
                assert(is_sorted_range(arr, 0, (i+1) as int));
            }
        }

        arr
   }
// </vc-code>

}
fn main() {}