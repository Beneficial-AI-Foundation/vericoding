// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn search(arr: Vec<i32>, target: i32) -> (result: i32)
    ensures
        arr.len() == 0 ==> result == -1,
        arr.len() > 0 ==> (
            (exists|i: int| 0 <= i < arr.len() && arr[i] == target) ==> 
            (result >= 0 && result < arr.len() && arr[result as int] == target)
        ),
        arr.len() > 0 ==> (
            (forall|i: int| 0 <= i < arr.len() ==> arr[i] != target) ==> 
            result == -1
        )
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    -1
    // impl-end
}
// </vc-code>


}

fn main() {
    // println!("{}", search(vec![4, 5, 6, 7, 0, 1, 2], 0));
    // println!("{}", search(vec![4, 5, 6, 7, 0, 1, 2], 3));
    // println!("{}", search(vec![1], 1));
}