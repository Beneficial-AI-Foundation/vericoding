// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Add exec function to call spec function from exec code */
exec fn fold_left_exec(arr: &Vec<f64>, index: usize) -> (result: f64)
    requires 
        arr.len() > 0,
        index < arr.len()
    ensures result == fold_left(arr@, index as nat)
{
    arr[index]
}
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
    /* code modified by LLM (iteration 2): Use exec helper instead of calling spec function directly */
    if arr.len() == 1 {
        arr[0]
    } else {
        fold_left_exec(&arr, arr.len() - 1)
    }
}
// </vc-code>

}
fn main() {}