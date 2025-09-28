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
{
    /* code modified by LLM (iteration 3): Added decreases clause to all while loops */
    let ghost ar1_seq = ar1@;
    let ghost ar2_seq = ar2@;
    
    let mut result: Vec<i32> = Vec::new();
    
    // Add elements from ar1 that are not in ar2
    let mut i: usize = 0;
    while i < ar1.len()
        invariant
            0 <= i <= ar1.len(),
            forall|j: int| 0 <= j < i ==> !contains_element(ar2_seq, ar1_seq[j]) ==> contains_element(result@, ar1_seq[j]),
            forall|x: i32| contains_element(result@, x) ==> (exists|j: int| 0 <= j < i && ar1_seq[j] == x && !contains_element(ar2_seq, x)),
        decreases ar1.len() - i
    {
        let elem = ar1[i];
        let mut found_in_ar2 = false;
        let mut j: usize = 0;
        
        while j < ar2.len()
            invariant
                0 <= j <= ar2.len(),
                found_in_ar2 <==> exists|k: int| 0 <= k < j && ar2_seq[k] == elem,
            decreases ar2.len() - j
        {
            if ar2[j] == elem {
                found_in_ar2 = true;
            }
            j = j + 1;
        }
        
        if !found_in_ar2 {
            result.push(elem);
        }
        i = i + 1;
    }
    
    // Add elements from ar2 that are not in ar1
    let mut i: usize = 0;
    while i < ar2.len()
        invariant
            0 <= i <= ar2.len(),
            forall|j: int| 0 <= j < ar1.len() ==> !contains_element(ar2_seq, ar1_seq[j]) ==> contains_element(result@, ar1_seq[j]),
            forall|j: int| 0 <= j < i ==> !contains_element(ar1_seq, ar2_seq[j]) ==> contains_element(result@, ar2_seq[j]),
            forall|x: i32| contains_element(result@, x) ==> in_exactly_one(ar1_seq, ar2_seq, x),
        decreases ar2.len() - i
    {
        let elem = ar2[i];
        let mut found_in_ar1 = false;
        let mut j: usize = 0;
        
        while j < ar1.len()
            invariant
                0 <= j <= ar1.len(),
                found_in_ar1 <==> exists|k: int| 0 <= k < j && ar1_seq[k] == elem,
            decreases ar1.len() - j
        {
            if ar1[j] == elem {
                found_in_ar1 = true;
            }
            j = j + 1;
        }
        
        if !found_in_ar1 {
            result.push(elem);
        }
        i = i + 1;
    }
    
    // Sort the result
    let mut i: usize = 0;
    while i < result.len()
        invariant
            0 <= i <= result.len(),
            forall|j: int, k: int| 0 <= j < k < i ==> result@[j] <= result@[k],
            forall|x: i32| contains_element(result@, x) ==> in_exactly_one(ar1_seq, ar2_seq, x),
            forall|x: i32| in_exactly_one(ar1_seq, ar2_seq, x) ==> contains_element(result@, x),
            has_no_duplicates(result@),
        decreases result.len() - i
    {
        let mut j: usize = i + 1;
        let mut min_idx: usize = i;
        
        while j < result.len()
            invariant
                i < j <= result.len(),
                i <= min_idx < result.len(),
                forall|k: int| i <= k < j ==> result@[min_idx as int] <= result@[k],
            decreases result.len() - j
        {
            if result[j] < result[min_idx] {
                min_idx = j;
            }
            j = j + 1;
        }
        
        if min_idx != i {
            let temp = result[i];
            result.set(i, result[min_idx]);
            result.set(min_idx, temp);
        }
        i = i + 1;
    }
    
    // Remove duplicates
    let mut unique_result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < result.len()
        invariant
            0 <= i <= result.len(),
            is_sorted(result@),
            has_no_duplicates(unique_result@),
            forall|j: int| 0 <= j < unique_result.len() ==> contains_element(result@, unique_result@[j]),
            forall|j: int| 0 <= j < i ==> contains_element(unique_result@, result@[j]) || (exists|k: int| 0 <= k < j && result@[k] == result@[j]),
            is_sorted(unique_result@),
        decreases result.len() - i
    {
        if i == 0 || result[i] != result[i - 1] {
            unique_result.push(result[i]);
        }
        i = i + 1;
    }
    
    unique_result
}
// </vc-code>


}
fn main() {}