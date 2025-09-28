// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add trigger annotations to fix quantifier verification */
spec fn is_consecutive(arr: Seq<i32>) -> bool {
    forall|i: int| 0 <= i < arr.len() - 1 ==> #[trigger] arr[i] + 1 == arr[i + 1]
}
proof fn lemma_consecutive_property(arr: Seq<i32>, i: int)
    requires
        0 <= i < arr.len() - 1,
    ensures
        arr[i] + 1 == arr[i + 1]
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
/* code modified by LLM (iteration 5): Fix loop invariant to properly handle consecutive check */
{
    let len = arr.len();
    assert(len > 0);
    
    let mut i: usize = 0;
    while i < len - 1
        invariant
            0 <= i <= len - 1,
            forall|k: int| 0 <= k < i ==> #[trigger] arr@[k] + 1 == arr@[k + 1],
        decreases (len - i) as int
    {
        if arr[i] + 1 != arr[i + 1] {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}