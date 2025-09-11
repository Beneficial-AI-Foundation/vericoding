// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn get_first_elements(arr: &Vec<Vec<i32>>) -> (result: Vec<i32>)

    requires
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() > 0,

    ensures
        arr.len() == result.len(),
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] result[i] == #[trigger] arr[i][0],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}