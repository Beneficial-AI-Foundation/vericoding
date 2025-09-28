// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Fixed quantifier trigger issue by splitting complex invariant */
    let mut sorted = arr.clone();
    let n = sorted.len();
    
    // Bubble sort
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            sorted.len() == n,
            sorted.len() == arr.len(),
            forall|k: int| 0 <= k < sorted.len() ==> arr@.contains(sorted@[k]),
            forall|val: i32| arr@.contains(val) ==> sorted@.contains(val),
            forall|p: int, q: int| 0 <= p < q < i && q < sorted.len() ==> sorted@[p] <= sorted@[q],
            forall|p: int| #[trigger] (0 <= p < i && p + 1 < sorted.len()) ==> sorted@[p] <= sorted@[p + 1],
        decreases n - i
    {
        let mut j: usize = 0;
        while j < n - 1
            invariant
                0 <= j <= n - 1,
                i < n,
                sorted.len() == n,
                forall|k: int| 0 <= k < sorted.len() ==> arr@.contains(sorted@[k]),
                forall|val: i32| arr@.contains(val) ==> sorted@.contains(val),
                forall|p: int, q: int| 0 <= p < q < i && q < sorted.len() ==> sorted@[p] <= sorted@[q],
                forall|p: int| #[trigger] (0 <= p < i && p + 1 < sorted.len()) ==> sorted@[p] <= sorted@[p + 1],
                forall|k: int| 0 <= k <= j as int ==> sorted@[k] <= sorted@[j as int],
            decreases n - 1 - j
        {
            if sorted[j] > sorted[j + 1] {
                let temp = sorted[j];
                sorted.set(j, sorted[j + 1]);
                sorted.set(j + 1, temp);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    // Remove duplicates
    let mut unique = Vec::new();
    let mut k: usize = 0;
    while k < sorted.len()
        invariant
            0 <= k <= sorted.len(),
            has_no_duplicates(unique@),
            is_sorted(unique@),
            is_sorted(sorted@),
            all_elements_from_input(unique@, arr@),
            forall|val: i32| #[trigger] sorted@.subrange(0, k as int).contains(val) ==> unique@.contains(val),
            forall|p: int| 0 <= p < unique.len() ==> sorted@.contains(unique@[p]),
        decreases sorted.len() - k
    {
        if k == 0 || sorted[k] != sorted[k - 1] {
            unique.push(sorted[k]);
        }
        k = k + 1;
    }
    
    let result_len = unique.len();
    (result_len, unique)
}
// </vc-code>


}
fn main() {}