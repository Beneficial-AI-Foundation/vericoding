// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed invariant syntax with proper requires and ensures */
spec fn contains_vec_spec(vec: &Vec<i32>, value: i32) -> bool {
    vec@.contains(value)
}

fn contains_vec_exec(vec: &Vec<i32>, value: i32) -> (result: bool)
    ensures result == contains_vec_spec(vec, value)
{
    let mut i: usize = 0;
    while i < vec.len()
        invariant 0 <= i <= vec.len(),
        invariant forall|j: int| 0 <= j < i ==> vec[j as usize] != value
    {
        if vec[i] == value {
            return true;
        }
        i += 1;
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
/* code modified by LLM (iteration 5): Fixed type issues and result reference */
{
    let mut shared = Vec::new();
    let mut seen = Vec::new();
    
    let mut i = 0;
    while i < list1.len()
        invariant 0 <= i <= list1.len()
    {
        let elem = list1[i];
        if contains_vec_exec(list2, elem) && !contains_vec_exec(&seen, elem) {
            shared.push(elem);
            seen.push(elem);
        }
        i += 1;
    }
    
    shared
}
// </vc-code>

}
fn main() {}