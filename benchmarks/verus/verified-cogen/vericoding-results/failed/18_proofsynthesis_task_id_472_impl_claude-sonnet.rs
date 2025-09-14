// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified helpers and fixed trigger issues */
spec fn are_consecutive(a: i32, b: i32) -> bool { a + 1 == b }

proof fn consecutive_property(arr: &Vec<i32>, i: int)
    requires
        0 <= i < arr.len() - 1,
        are_consecutive(arr[i], arr[i + 1]),
    ensures
        arr[i] + 1 == arr[i + 1],
{
}

proof fn arithmetic_safety(arr: &Vec<i32>, i: int)
    requires
        0 <= i < arr.len(),
        forall|j: int| 0 <= j < arr.len() ==> (0 <= #[trigger] arr[j] + 1 < i32::MAX),
    ensures
        0 <= arr[i] + 1 < i32::MAX,
{
}
// </vc-helpers>

// <vc-spec>
fn contains_consecutive_numbers(arr: &Vec<i32>) -> (is_consecutive: bool)

    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> (0 <= #[trigger] arr[i] + 1 < i32::MAX),

    ensures
        is_consecutive == (forall|i: int, j: int|
            0 <= i < j < arr.len() && j == i + 1 ==> (arr[i] + 1 == arr[j])),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed trigger annotation placement and verification logic */
    if arr.len() == 1 {
        return true;
    }
    
    let mut i = 0;
    while i < arr.len() - 1
        invariant
            0 <= i <= arr.len() - 1,
            arr.len() > 1,
            forall|k: int| 0 <= k < i ==> #[trigger] arr[k] + 1 == #[trigger] arr[k + 1],
        decreases arr.len() - 1 - i
    {
        proof {
            arithmetic_safety(arr, i as int);
        }
        if arr[i] + 1 != arr[i + 1] {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-code>

}
fn main() {}