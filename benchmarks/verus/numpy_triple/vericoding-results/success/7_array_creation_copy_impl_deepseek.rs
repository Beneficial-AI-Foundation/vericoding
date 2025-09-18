// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix nat usage in exec context by using usize instead */
fn copy_helper<T: Copy>(a: &Vec<T>, i: usize) -> (result: Vec<T>)
    requires
        0 <= i <= a.len(),
    ensures
        result.len() == a.len() - i,
        forall|j: int| 0 <= j < a.len() - i ==> result@[j] == a@[i + j],
    decreases a.len() - i,
{
    if i >= a.len() {
        Vec::new()
    } else {
        let mut result = copy_helper(a, i + 1);
        result.insert(0, a[i]);
        result
    }
}
// </vc-helpers>

// <vc-spec>
fn copy<T: Copy>(a: &Vec<T>) -> (result: Vec<T>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Use usize instead of nat for exec context */
{
    let result = copy_helper(a, 0);
    result
}
// </vc-code>

}
fn main() {}