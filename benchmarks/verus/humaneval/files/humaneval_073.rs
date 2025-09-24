// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_mismatched_pairs(arr: Seq<int>) -> int {
    count_mismatched_pairs_up_to(arr, arr.len() as int / 2)
}

spec fn count_mismatched_pairs_up_to(arr: Seq<int>, limit: int) -> int
    decreases limit
{
    if limit <= 0 || limit > arr.len() as int / 2 {
        0 as int
    } else if limit == 0 {
        0 as int
    } else {
        (if arr[limit - 1] != arr[arr.len() as int - limit] { 1 as int } else { 0 as int }) +
        count_mismatched_pairs_up_to(arr, limit - 1)
    }
}

spec fn can_make_palindromic_with_changes(arr: Seq<int>, num_changes: int) -> bool {
    num_changes >= 0 && num_changes >= count_mismatched_pairs(arr)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn smallest_change(arr: Vec<i8>) -> (changes: usize)
    ensures 
        changes <= arr@.len() / 2,
        changes as int == count_mismatched_pairs(arr@.map(|i, x| x as int)),
        arr@.len() <= 1 ==> changes == 0,
        ({
            let arr_int = arr@.map(|i, x| x as int);
            forall|c: int| can_make_palindromic_with_changes(arr_int, c) ==> (0 <= c < changes as int ==> !can_make_palindromic_with_changes(arr_int, c))
        }),
        ({
            let arr_int = arr@.map(|i, x| x as int);
            can_make_palindromic_with_changes(arr_int, changes as int)
        })
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}

fn main() {}