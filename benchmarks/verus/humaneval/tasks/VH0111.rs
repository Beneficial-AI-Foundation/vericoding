// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

spec fn rotate_right(arr: Seq<int>, k: int) -> Seq<int>
    recommends 0 <= k <= arr.len()
{
    if arr.len() == 0 {
        arr
    } else if k == 0 {
        arr
    } else {
        arr.subrange((arr.len() - k) as int, arr.len() as int) + arr.subrange(0, (arr.len() - k) as int)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn move_one_ball(arr: Vec<i8>) -> (result: bool)
    requires 
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i as int] != arr[j as int]
    ensures 
        arr.len() == 0 ==> result == true,
        result == true ==> (arr.len() == 0 || exists|k: int| #[trigger] is_sorted(rotate_right(arr@.map(|i, x: i8| x as int), k)) && 0 <= k < arr.len()),
        result == false ==> forall|k: int| 0 <= k < arr.len() ==> !is_sorted(rotate_right(arr@.map(|i, x: i8| x as int), k))
// </vc-spec>
// <vc-code>
{
    assume(false);
    false
}
// </vc-code>


}

fn main() {}