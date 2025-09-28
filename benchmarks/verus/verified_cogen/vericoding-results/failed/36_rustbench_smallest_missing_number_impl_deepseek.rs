// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix binary_search_helper types and indexing */
proof fn lemma_sorted_array_contains_all_below_max(s: Seq<i32>, max: int)
    requires
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
        max >= 0,
        forall|i: int| 0 <= i < s.len() ==> s[i] != max,
        s.len() > max,
    ensures
        exists|j: int| 0 <= j < s.len() && s[j] == max,
{
}

proof fn lemma_sorted_array_missing_number_gap(s: Seq<i32>, idx: int)
    requires
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
        0 <= idx < s.len(),
        s[idx] > idx,
    ensures
        forall|k: int| idx <= k < s[idx] ==> exists|j: int| 0 <= j < s.len() && s[j] != k,
{
}

fn binary_search_helper(s: Seq<i32>, low: int, high: int, target: i32) -> (result: bool)
    requires
        0 <= low <= high <= s.len(),
    ensures
        result == exists|i: int| low <= i < high && s[i] == target
{
    if low >= high {
        false
    } else {
        let mid: int = low + (high - low) / 2;
        if s[mid as usize] == target {
            true
        } else if s[mid as usize] < target {
            binary_search_helper(s, mid + 1, high, target)
        } else {
            binary_search_helper(s, low, mid, target)
        }
    }
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn smallest_missing_number(s: &[i32]) -> (v: i32)
    requires
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
        s.len() <= 100_000,
    ensures
        0 <= v,
        forall|i: int| 0 <= i < s.len() ==> s[i] != v,
        forall|k: int| 0 <= k < v && s[k] != v ==> exists|j: int| 0 <= j < s.len() && s[j] == k,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix type conversion and indexing */
{
    let mut low: usize = 0;
    let mut high: usize = s.len();
    let result: i32;
    
    while low < high
        invariant
            0 <= low <= high <= s.len(),
            forall|i: int| 0 <= i < low ==> s[i] == i,
            forall|k: int| low <= k < high && low > 0 ==> s[k] != k,
            forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
            forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j],
    {
        let mid: usize = low + (high - low) / 2;
        
        if s[mid] == mid as i32 {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    
    result = low as i32;
    result
}
// </vc-code>

}
fn main() {}