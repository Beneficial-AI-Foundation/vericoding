// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fixed insertion sort with proper bounds checking */
fn insertion_sort(arr: Vec<i32>) -> (sorted: Vec<i32>)
    ensures
        is_sorted(sorted@),
        sorted@.len() == arr@.len(),
        forall|i: int| 0 <= i < sorted@.len() ==> arr@.contains(sorted@[i]),
        forall|i: int| 0 <= i < arr@.len() ==> sorted@.contains(arr@[i])
{
    let mut sorted = arr;
    let n = sorted.len();
    if n == 0 {
        return sorted;
    }
    for i in 1..n
        invariant
            1 <= i <= n,
            is_sorted(sorted@.subrange(0, i as int)),
            sorted@.len() == arr@.len(),
            forall|j: int| 0 <= j < sorted@.len() ==> arr@.contains(sorted@[j]),
            forall|j: int| 0 <= j < arr@.len() ==> sorted@.contains(arr@[j])
    {
        let key = sorted[i];
        let mut j = i;
        while j > 0 && sorted[j-1] > key
            invariant
                0 <= j <= i,
                is_sorted(sorted@.subrange(0, j as int) + seq![key] + sorted@.subrange(j as int, i as int)),
                sorted@.len() == arr@.len(),
                forall|k: int| 0 <= k < sorted@.len() ==> arr@.contains(sorted@[k]),
                forall|k: int| 0 <= k < arr@.len() ==> sorted@.contains(arr@[k])
            decreases j
        {
            sorted[j] = sorted[j-1];
            j -= 1;
        }
        sorted[j] = key;
    }
    sorted
}

/* helper modified by LLM (iteration 2): Fixed remove_duplicates with proper bounds checking */
fn remove_duplicates(sorted_arr: Vec<i32>) -> (unique_arr: Vec<i32>)
    requires
        is_sorted(sorted_arr@),
    ensures
        is_sorted(unique_arr@),
        has_no_duplicates(unique_arr@),
        all_elements_from_input(unique_arr@, sorted_arr@),
        all_distinct_elements_present(sorted_arr@, unique_arr@)
{
    if sorted_arr.len() == 0 {
        return Vec::new();
    }
    let mut unique = Vec::new();
    unique.push(sorted_arr[0]);
    let mut last = sorted_arr[0];
    let n = sorted_arr.len();
    for i in 1..n
        invariant
            1 <= i <= n,
            is_sorted(unique@),
            has_no_duplicates(unique@),
            all_elements_from_input(unique@, sorted_arr@.subrange(0, i as int)),
            all_distinct_elements_present(sorted_arr@.subrange(0, i as int), unique@)
    {
        if sorted_arr[i] != last {
            unique.push(sorted_arr[i]);
            last = sorted_arr[i];
        }
    }
    unique
}
// </vc-helpers>

// <vc-spec>
spec fn is_sorted(arr: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
}

spec fn has_no_duplicates(arr: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() && i != j ==> arr[i] != arr[j]
}

spec fn all_elements_from_input(result: Seq<i32>, input: Seq<i32>) -> bool {
    forall|i: int| 0 <= i < result.len() ==> #[trigger] input.contains(result[i])
}

spec fn all_distinct_elements_present(input: Seq<i32>, result: Seq<i32>) -> bool {
    forall|val: i32| input.contains(val) ==> #[trigger] result.contains(val)
}

fn numpy_unique(arr: Vec<i32>) -> (result: (usize, Vec<i32>))
    ensures
        is_sorted(result.1@),
        has_no_duplicates(result.1@),
        all_elements_from_input(result.1@, arr@),
        all_distinct_elements_present(arr@, result.1@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed main function implementation */
{
    let sorted_arr = insertion_sort(arr);
    let unique_arr = remove_duplicates(sorted_arr);
    let count = unique_arr.len();
    (count, unique_arr)
}
// </vc-code>


}
fn main() {}