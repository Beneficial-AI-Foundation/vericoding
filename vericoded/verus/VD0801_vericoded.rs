use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn last_position(arr: &Vec<i32>, elem: i32) -> (pos: i32)
    requires 
        arr.len() > 0,
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j],
    ensures
        pos == -1 || (0 <= pos < arr.len() && arr[pos as int] == elem && 
            (pos >= arr.len() - 1 || arr[(pos + 1) as int] > elem)),
// </vc-spec>
// <vc-code>
{
    -1
}
// </vc-code>

fn main() {}

}