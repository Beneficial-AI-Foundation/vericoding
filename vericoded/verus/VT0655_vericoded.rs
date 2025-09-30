// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn fold_left(arr: Seq<f64>, index: nat) -> f64
    decreases index
{
    if index == 0 {
        arr[0 as int]
    } else {

        arr[index as int]
    }
}

fn reduce(arr: Vec<f64>) -> (result: f64)
    requires arr.len() > 0,
    ensures 
        arr.len() == 1 ==> result == arr[0],
        arr.len() > 1 ==> result == fold_left(arr@, (arr.len() - 1) as nat)
// </vc-spec>
// <vc-code>
{
    let len = arr.len();
    if len == 1 {
        let r = arr[0];
        r
    } else {
        let idx = len - 1;
        assert(idx < arr.len());
        let r = arr[idx];
        r
    }
}
// </vc-code>

}
fn main() {}