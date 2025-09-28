// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): trivial vector length non-negativity helper */
spec fn vec_len_nonneg(arr: &Vec<i32>) -> bool { arr.len() >= 0 }
// </vc-helpers>

// <vc-spec>
fn contains_k(arr: &Vec<i32>, k: i32) -> (result: bool)

    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == k)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): use usize index and prove final result matches spec */
    let mut i: usize = 0;
    let mut found: bool = false;
    while i < arr.len()
        invariant
            found == (exists|j: int| 0 <= j < i as int && arr[j] == k),
            i <= arr.len(),
        decreases
            arr.len() - i
    {
        if arr[i] == k {
            found = true;
        }
        i = i + 1;
    }
    proof {
        assert(!(i < arr.len()));
        assert(i >= arr.len());
        assert(i <= arr.len());
        assert(i == arr.len());
        assert(found == (exists|j: int| 0 <= j < i as int && arr[j] == k));
        assert(found == (exists|j: int| 0 <= j < arr.len() && arr[j] == k));
    }
    found
}
// </vc-code>

}
fn main() {}