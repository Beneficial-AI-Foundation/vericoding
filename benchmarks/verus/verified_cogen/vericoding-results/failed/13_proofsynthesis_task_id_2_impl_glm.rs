// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added exec function to check vector containment */
exec fn contains_vec(v: &Vec<i32>, x: i32) -> bool {
    for i in 0..v.len() {
        if v[i] == x {
            return true;
        }
    }
    false
}
// </vc-helpers>

// <vc-spec>
fn shared_elements(list1: &Vec<i32>, list2: &Vec<i32>) -> (shared: Vec<i32>)

    ensures
        forall|i: int|
            0 <= i < shared.len() ==> (list1@.contains(#[trigger] shared[i]) && list2@.contains(
                #[trigger] shared[i],
            )),
        forall|i: int, j: int| 0 <= i < j < shared.len() ==> shared[i] != shared[j],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): replaced spec contains with exec contains_vec */
{
    let mut result: Vec<i32> = Vec::new();
    for i in 0..list1.len() {
        let x = list1[i];
        if contains_vec(list2, x) && !contains_vec(&result, x) {
            result.push(x);
        }
    }
    result
}
// </vc-code>

}
fn main() {}