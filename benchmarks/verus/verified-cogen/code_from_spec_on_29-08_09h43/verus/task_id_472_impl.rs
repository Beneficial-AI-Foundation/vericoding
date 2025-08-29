use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_consecutive_property(arr: &Vec<i32>, idx: int)
    requires
        arr.len() > 1,
        0 <= idx < arr.len() - 1,
        forall|i: int| 0 <= i < arr.len() ==> (0 <= arr[i] + 1 < i32::MAX),
        forall|k: int, l: int| 0 <= k < l < idx + 1 && l == k + 1 ==> (arr[k] + 1 == arr[l]),
        arr[idx] + 1 == arr[idx + 1],
    ensures
        forall|k: int, l: int| 0 <= k < l < idx + 2 && l == k + 1 ==> (arr[k] + 1 == arr[l]),
{
    assert forall|k: int, l: int| 0 <= k < l < idx + 2 && l == k + 1 implies (arr[k] + 1 == arr[l]) by {
        if k == idx && l == idx + 1 {
            assert(arr[k] + 1 == arr[l]);
        } else if 0 <= k < l < idx + 1 && l == k + 1 {
            assert(arr[k] + 1 == arr[l]);
        }
    }
}
// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

// <vc-spec>
fn contains_consecutive_numbers(arr: &Vec<i32>) -> (is_consecutive: bool)
    // pre-conditions-start
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> (0 <= #[trigger] arr[i] + 1 < i32::MAX),
    // pre-conditions-end
    // post-conditions-start
    ensures
        is_consecutive == (forall|i: int, j: int|
            0 <= i < j < arr.len() && j == i + 1 ==> (arr[i] + 1 == arr[j])),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    // impl-start
    if arr.len() == 1 {
        return true;
    }
    
    let mut i = 0;
    /* code modified by LLM (iteration 5): fixed type mismatches by casting usize to int */
    while i < arr.len() - 1
        invariant
            0 <= i <= arr.len() - 1,
            forall|k: int, l: int| 0 <= k < l <= i && l == k + 1 ==> (arr[k] + 1 == arr[l]),
        decreases arr.len() - 1 - i,
    {
        /* code modified by LLM (iteration 5): cast usize i to int for array indexing */
        assert(0 <= arr[i as int] + 1 < i32::MAX);
        if arr[i] + 1 != arr[i + 1] {
            return false;
        }
        /* code modified by LLM (iteration 5): cast usize i to int for lemma call */
        proof {
            lemma_consecutive_property(arr, i as int);
        }
        i += 1;
    }
    true
    // impl-end
}
// </vc-code>

} // verus!

fn main() {}