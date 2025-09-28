// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn contains_element(arr: Seq<i32>, elem: i32) -> bool {
    exists|i: int| 0 <= i < arr.len() && arr[i] == elem
}

spec fn is_sorted(arr: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
}

spec fn has_no_duplicates(arr: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() && i != j ==> arr[i] != arr[j]
}

spec fn in_exactly_one(ar1: Seq<i32>, ar2: Seq<i32>, elem: i32) -> bool {
    (contains_element(ar1, elem) && !contains_element(ar2, elem)) ||
    (contains_element(ar2, elem) && !contains_element(ar1, elem))
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_setxor1d(ar1: &Vec<i32>, ar2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        /* Result is sorted */
        is_sorted(result@),
        /* Result has no duplicates */
        has_no_duplicates(result@),
        /* Every element in result is from exactly one input array */
        forall|i: int| 0 <= i < result.len() ==> #[trigger] in_exactly_one(ar1@, ar2@, result[i]),
        /* Every element that appears in exactly one input array is in the result */
        forall|x: i32| in_exactly_one(ar1@, ar2@, x) ==> contains_element(result@, x)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error related to `complex arguments to &mut parameters` by creating a new Vec for sorting. */
{
    let mut result_vec: Vec<i32> = Vec::new();
    let ar1_seq = ar1@;
    let ar2_seq = ar2@;

    let mut ar1_deduped: Vec<i32> = Vec::new();
    let mut ar2_deduped: Vec<i32> = Vec::new();

    // Populate ar1_deduped
    let mut temp1 = ar1.clone();
    temp1.sort();
    if temp1.len() > 0 {
        ar1_deduped.push(temp1[0]);
        let mut i: usize = 1;
        while i < temp1.len()
            invariant
                0 <= i && i <= temp1.len(),
                ar1_deduped.len() <= i,
                forall|k: int| 0 <= k < ar1_deduped.len() ==> (
                    contains_element(ar1_seq, ar1_deduped@[k])
                ),
                has_no_duplicates(ar1_deduped@),
                is_sorted(ar1_deduped@)
            decreases temp1.len() - i
        {
            if temp1[i] != *ar1_deduped.last().tracked_unwrap() {
                ar1_deduped.push(temp1[i]);
            }
            i = i + 1;
        }
    }

    // Populate ar2_deduped
    let mut temp2 = ar2.clone();
    temp2.sort();
    if temp2.len() > 0 {
        ar2_deduped.push(temp2[0]);
        let mut i: usize = 1;
        while i < temp2.len()
            invariant
                0 <= i && i <= temp2.len(),
                ar2_deduped.len() <= i,
                forall|k: int| 0 <= k < ar2_deduped.len() ==> (
                    contains_element(ar2_seq, ar2_deduped@[k])
                ),
                has_no_duplicates(ar2_deduped@),
                is_sorted(ar2_deduped@)
            decreases temp2.len() - i
        {
            if temp2[i] != *ar2_deduped.last().tracked_unwrap() {
                ar2_deduped.push(temp2[i]);
            }
            i = i + 1;
        }
    }

    let mut i: usize = 0;
    let mut j: usize = 0;

    while i < ar1_deduped.len() || j < ar2_deduped.len()
        invariant
            0 <= i && i <= ar1_deduped.len(),
            0 <= j && j <= ar2_deduped.len(),
            is_sorted(result_vec@),
            has_no_duplicates(result_vec@),
            forall|k: int| 0 <= k < result_vec.len() ==> in_exactly_one(ar1_seq, ar2_seq, result_vec@[k]),
            forall|idx_m: int| 0 <= idx_m < i ==> ( (contains_element(ar1_seq, ar1_deduped@[idx_m]) && !contains_element(ar2_seq, ar1_deduped@[idx_m])) ==> 
                contains_element(result_vec@, ar1_deduped@[idx_m])) || ( 
                (contains_element(ar1_seq, ar1_deduped@[idx_m]) && contains_element(ar2_seq, ar1_deduped@[idx_m])) ||
                (!contains_element(ar1_seq, ar1_deduped@[idx_m]))) 
            ,
            forall|idx_n: int| 0 <= idx_n < j ==> ( (contains_element(ar2_seq, ar2_deduped@[idx_n]) && !contains_element(ar1_seq, ar2_deduped@[idx_n])) ==> 
                contains_element(result_vec@, ar2_deduped@[idx_n])) || ( 
                (contains_element(ar2_seq, ar2_deduped@[idx_n]) && contains_element(ar1_seq, ar2_deduped@[idx_n])) ||
                (!contains_element(ar2_seq, ar2_deduped@[idx_n])))           
        decreases ar1_deduped.len() - i + ar2_deduped.len() - j
    {
        if i < ar1_deduped.len() && (j == ar2_deduped.len() || ar1_deduped[i] < ar2_deduped[j]) {
            let elem = ar1_deduped[i];
            if !contains_element(ar2_seq, elem) {
                result_vec.push(elem);
            }
            i = i + 1;
        } else if j < ar2_deduped.len() && (i == ar1_deduped.len() || ar2_deduped[j] < ar1_deduped[i]) {
            let elem = ar2_deduped[j];
            if !contains_element(ar1_seq, elem) {
                result_vec.push(elem);
            }
            j = j + 1;
        } else if i < ar1_deduped.len() && j < ar2_deduped.len() && ar1_deduped[i] == ar2_deduped[j] {
            i = i + 1;
            j = j + 1;
        } else {
             // This branch should ideally not be reached if the loop conditions and logic are exhaustive.
             // For a formally verified proof, we need to ensure all cases covered by the loop condition are handled.
             // Since i<ar1_deduped.len() and j<ar2_deduped.len() are exhausted, the remaining conditions are i==ar1_deduped.len() and j==ar2_deduped.len().
             // If both are true, the loop terminates.
             // If one is true and the other is false, it's covered by the first two 'if' branches.
        }
    }

    result_vec
}
// </vc-code>


}
fn main() {}