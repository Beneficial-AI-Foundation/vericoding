// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added decreases clauses for helper functions */

    spec fn is_strictly_sorted(s: Seq<i32>) -> bool {
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] < s[j]
    }

    spec fn elements_match(arr: Seq<i32>, result: Seq<i32>) -> bool {
        forall|i: int| 0 <= i < result.len() ==> exists|j: int| 0 <= j < arr.len() && result[i] == arr[j]
    }

    spec fn all_elements_present(arr: Seq<i32>, result: Seq<i32>) -> bool {
        forall|i: int| 0 <= i < arr.len() ==> exists|j: int| 0 <= j < result.len() && arr[i] == result[j]
    }

    spec fn contains_no_duplicates(s: Seq<i32>) -> bool {
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j]
    }
// </vc-helpers>

// <vc-spec>
fn unique(arr: Vec<i32>) -> (result: Vec<i32>)
    ensures

        forall|i: int, j: int| #![trigger result[i], result[j]] 0 <= i < j < result.len() ==> result[i] < result[j],

        forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==> exists|j: int| 0 <= j < arr.len() && result[i] == arr[j],

        forall|i: int, j: int| #![trigger result[i], result[j]] 0 <= i < result.len() && 0 <= j < result.len() && i != j ==> result[i] != result[j],

        forall|i: int| #![trigger arr[i]] 0 <= i < arr.len() ==> exists|j: int| 0 <= j < result.len() && arr[i] == result[j],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Added decreases clauses to all while loops */
{
    let mut temp = arr.clone();
    
    // Sort the array
    let mut i: usize = 0;
    while i < temp.len()
        decreases temp.len() - i,
    {
        let mut j: usize = 0;
        while j < temp.len() - i - 1
            decreases (temp.len() - i - 1) - j,
        {
            if temp[j] > temp[j + 1] {
                let swap = temp[j];
                temp[j] = temp[j + 1];
                temp[j + 1] = swap;
            }
            j += 1;
        }
        i += 1;
    }
    
    let mut result: Vec<i32> = Vec::new();
    
    if temp.len() > 0 {
        result.push(temp[0]);
        let mut k: usize = 1;
        while k < temp.len()
            decreases temp.len() - k,
        {
            if temp[k] != temp[k - 1] {
                result.push(temp[k]);
            }
            k += 1;
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}