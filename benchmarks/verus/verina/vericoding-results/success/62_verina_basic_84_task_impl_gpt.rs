// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fix int/i32 mismatch in elem_prop conditional */
spec fn elem_prop(x: i32, k: i32, y: i32) -> bool {
    if x > k { y == -1i32 } else { y == x }
}

/* helper modified by LLM (iteration 2): fix int/i32 mismatch in ensures expression */
proof fn lemma_elem_prop(x: i32, k: i32)
    ensures elem_prop(x, k, if x > k { -1i32 } else { x })
{
}

// </vc-helpers>

// <vc-spec>
fn replace(arr: &Vec<i32>, k: i32) -> (result: Vec<i32>)
    ensures
        result.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> (arr[i] > k ==> result[i] == -1),
        forall|i: int| 0 <= i < arr.len() ==> (arr[i] <= k ==> result[i] == arr[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implement replace with loop and invariants */
    let mut res: Vec<i32> = Vec::new();
    while res.len() < arr.len()
        invariant
            res.len() <= arr.len(),
            forall|j: int| 0 <= j < res.len() ==> (arr[j] > k ==> res[j] == -1i32),
            forall|j: int| 0 <= j < res.len() ==> (arr[j] <= k ==> res[j] == arr[j]),
        decreases arr.len() - res.len()
    {
        let i = res.len();
        let a = arr[i];
        if a > k {
            res.push(-1);
        } else {
            res.push(a);
        }
    }
    res
}
// </vc-code>

}
fn main() {}