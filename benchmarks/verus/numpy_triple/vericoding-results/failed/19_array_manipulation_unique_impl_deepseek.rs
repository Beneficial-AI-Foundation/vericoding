// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type comparison issues */
fn find_min_index(arr: &Vec<i32>, start: usize, end: usize) -> (min_index: usize)
    requires
        0 <= start < end <= arr.len(),
    ensures
        start <= min_index < end,
        forall|k: int| start <= k < end ==> arr[min_index] as int <= arr[k as usize] as int
{
    let mut min_index = start;
    let mut i = start + 1;
    
    while i < end
        invariant
            start <= min_index < i,
            forall|k: int| start <= k < i ==> arr[min_index] as int <= arr[k as usize] as int
        decreases end - i
    {
        if arr[i] < arr[min_index] {
            min_index = i;
        }
        i += 1;
    }
    
    min_index
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
{
    /* code modified by LLM (iteration 5): Fixed subrange method usage with proper slicing */
    if arr.is_empty() {
        return (0, Vec::new());
    }
    
    let mut result = arr.clone();
    let mut len = result.len();
    
    // Remove duplicates while preserving sorted order
    let mut i = 0;
    let mut j = 1;
    
    while j < result.len()
        invariant
            0 <= i < j <= result.len(),
            is_sorted(result@.subrange(0, j as int)),
            has_no_duplicates(result@.subrange(0, j as int)),
            all_elements_from_input(result@.subrange(0, j as int), arr@),
            all_distinct_elements_present(arr@, result@.subrange(0, j as int))
        decreases result.len() - j
    {
        if result[i] != result[j] {
            i += 1;
            result[i] = result[j];
        }
        j += 1;
    }
    
    result.truncate(i + 1);
    len = result.len();
    
    (len, result)
}
// </vc-code>


}
fn main() {}