// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed redundant `result: nat` type annotation. */
spec fn count_distinct_in_prefix(s: Seq<i32>) -> nat
    requires s.len() >= 0
    ensures (result) => 
        if s.len() == 0 { result == 0 }
        else if s.len() == 1 { result == 1 }
        else {
            let mut count = 1;
            let mut k = 1;
            while k < s.len()
                invariant
                    1 <= k <= s.len(),
                    1 <= count <= k + 1,
                    forall |m: int| 0 <= m < k ==> s[m] <= s[m+1]
                decreases s.len() - k
            {
                if s[k] > s[k-1] {
                    count = count + 1;
                }
                k = k + 1;
            }
            count == result
        }
{
    if s.len() == 0 { 0 }
    else if s.len() == 1 { 1 }
    else {
        let mut count = 1;
        let mut k = 1;
        while k < s.len()
            invariant
                1 <= k <= s.len(),
                1 <= count <= k + 1,
                forall |m: int| 0 <= m < k ==> s[m] <= s[m+1] // All elements up to k are sorted
            decreases s.len() - k
        {
            if s[k] > s[k-1] {
                count = count + 1;
            }
            k = k + 1;
        }
        count
    }
}

spec fn count_distinct_in_prefix_recursive(s: Seq<i32>) -> nat
    requires s.len() >= 0
    ensures (result) => {
        if s.len() == 0 { result == 0 }
        else if s.len() == 1 { result == 1 }
        else { (s[s.len() - 1] > s[s.len() - 2] ? 1 : 0) + count_distinct_in_prefix_recursive(s.subrange(0, s.len() - 1)) == result }
    }
{
    if s.len() == 0 { 0 }
    else if s.len() == 1 { 1 }
    else {
        (s[s.len() as int - 1] > s[s.len() as int - 2] ? 1 : 0) + count_distinct_in_prefix_recursive(s.subrange(0, s.len() as int - 1))
    }
}

spec fn new_empty_vec() -> Vec<i32>
{
    Vec::new()
}
// </vc-helpers>

// <vc-spec>
fn unique_sorted(arr: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() <= arr.len(),
        forall|i: int| 0 <= i < result.len() - 1 ==> #[trigger] result[i] <= result[i + 1],
        forall|x: i32| arr@.contains(x) <==> result@.contains(x),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added `mut` keyword to `result` in ensires clause */
fn unique_sorted(arr: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() <= arr.len(),
        forall|i: int| 0 <= i < result.len() - 1 ==> #[trigger] result[i] <= result[i + 1],
        forall|x: i32| arr@.contains(x) <==> result@.contains(x),
{
    let mut result_vec = Vec::new();
    let mut arr_sorted: Vec<i32> = Vec::new();
    arr_sorted.clone_from(arr);
    arr_sorted.sort_unstable();

    let mut i: int = 0; let mut j: int = 0;

    while j < arr_sorted.len()
        invariant 
            0 <= i <= j,
            0 <= j <= arr_sorted.len(),
            result_vec.len() == i,
            // result_vec contains unique sorted elements from arr_sorted[0..j]
            forall |k: int| 0 <= k < i ==> 
                (
                    (k == 0 ==> arr_sorted[0] == result_vec[k])
                    && (k > 0 ==> result_vec[k-1] < result_vec[k] && result_vec[k] == arr_sorted[j - (j-i) - (i-k)])
                ),
            // All elements in result_vec are from arr_sorted[0..j]
            forall |k: int| 0 <= k < i ==> arr_sorted@.subrange(0, j)@.contains(result_vec[k]),
            // All unique elements up to j are present in result_vec
            forall |x: i32| (exists |k: int| 0 <= k < arr_sorted.len() && x == arr_sorted[k] && k < j) ==> result_vec@.contains(x),
            result_vec.len() == ( // Updated with `count_distinct_in_prefix`
                if j == 0 { 0 }
                else {
                    count_distinct_in_prefix(arr_sorted@.subrange(0, j))
                }
            )
        decreases arr_sorted.len() - j
    {
        if i == 0 || arr_sorted[j] > result_vec[i - 1] {
            result_vec.push(arr_sorted[j]);
            i = i + 1;
        }
        j = j + 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}