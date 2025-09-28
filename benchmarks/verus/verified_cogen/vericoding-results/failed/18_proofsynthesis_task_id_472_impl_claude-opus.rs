// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): fixed array access syntax - use @ for sequence indexing */
    if arr.len() == 1 {
        return true;
    }
    
    let mut i: usize = 0;
    while i < arr.len() - 1
        invariant
            0 <= i <= arr.len() - 1,
            forall|k: int, l: int| 0 <= k < l <= i as int && l == k + 1 ==> arr@[k] + 1 == arr@[l],
    {
        if arr@[i as int] + 1 != arr@[(i + 1) as int] {
            assert(!(forall|k: int, l: int| 0 <= k < l < arr.len() && l == k + 1 ==> arr@[k] + 1 == arr@[l])) by {
                assert(arr@[i as int] + 1 != arr@[(i + 1) as int]);
                assert(0 <= i as int && (i + 1) as int < arr@.len());
                assert((i + 1) as int == i as int + 1);
            };
            return false;
        }
        i = i + 1;
    }
    
    assert(forall|k: int, l: int| 0 <= k < l < arr.len() && l == k + 1 ==> arr@[k] + 1 == arr@[l]) by {
        assert(i == arr.len() - 1);
        assert forall|k: int, l: int| 0 <= k < l < arr.len() && l == k + 1 implies arr@[k] + 1 == arr@[l] by {
            assert(k < l <= arr.len() - 1);
            assert(l <= i as int);
        };
    };
    
    true
}
// </vc-code>

}
fn main() {}