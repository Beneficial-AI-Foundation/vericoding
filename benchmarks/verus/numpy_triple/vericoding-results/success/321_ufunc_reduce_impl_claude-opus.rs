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
    /* code modified by LLM (iteration 2): Added decreases clause to while loop */
    let mut result = arr[0];
    let mut i: usize = 1;
    while i < arr.len()
        invariant
            1 <= i <= arr.len(),
            arr.len() == 1 ==> result == arr[0],
            i == 1 ==> result == arr[0],
            i > 1 ==> result == fold_left(arr@, (i - 1) as nat),
        decreases arr.len() - i
    {
        result = arr[i as usize];
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}