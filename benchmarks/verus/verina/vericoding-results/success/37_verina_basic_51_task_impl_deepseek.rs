// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn binary_search_precond(a: &Vec<i32>, key: i32) -> bool {
    forall|i: int, j: int| 0 <= i <= j < a.len() ==> a[i] <= a[j]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Added is_sorted helper function to fix compilation errors */
spec fn is_sorted(a: &Vec<i32>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < a.len() ==> a[i] <= a[j]
}

/* helper modified by LLM (iteration 3): Fixed type mismatches in binary_search_helper parameters */
proof fn binary_search_helper(a: &Vec<i32>, key: i32, low: int, high: int)
    requires
        is_sorted(a),
        0 <= low <= high <= a.len(),
        forall|i: int| 0 <= i < low ==> a[i] < key,
        forall|i: int| high <= i < a.len() ==> a[i] >= key
    ensures
        forall|i: int| 0 <= i < low ==> a[i] < key,
        forall|i: int| high <= i < a.len() ==> a[i] >= key
{
    // The lemma body maintains the invariants
    // No additional proof needed for the given specifications
}
// </vc-helpers>

// <vc-spec>
fn binary_search(a: &Vec<i32>, key: i32) -> (result: usize)
    requires binary_search_precond(a, key),
    ensures
        result <= a.len(),
        forall|i: int| 0 <= i < result ==> a[i] < key,
        forall|i: int| result <= i < a.len() ==> a[i] >= key,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed compilation errors by ensuring proper type usage */
{
    let mut low: usize = 0;
    let mut high: usize = a.len();
    
    while low < high
        invariant
            is_sorted(a),
            0 <= low <= high <= a.len(),
            forall|i: int| 0 <= i < low ==> a[i] < key,
            forall|i: int| high <= i < a.len() ==> a[i] >= key
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        
        if a[mid] < key {
            proof { binary_search_helper(a, key, (mid + 1) as int, high as int); }
            low = mid + 1;
        } else {
            proof { binary_search_helper(a, key, low as int, mid as int); }
            high = mid;
        }
    }
    
    low
}
// </vc-code>

}
fn main() {}