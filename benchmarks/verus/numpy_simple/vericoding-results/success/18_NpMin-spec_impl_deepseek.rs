// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add decreases clause to recursive function */
fn min_index(a: &Vec<i8>, n: usize) -> (idx: usize)
    requires
        n <= a.len(),
        n > 0,
    ensures
        idx < n,
        forall|i: int| 0 <= i < n ==> a@[idx as int] <= a@[i]
    decreases n
{
    if n == 1 {
        0
    } else {
        let prev_idx = min_index(a, n - 1);
        if a[prev_idx] <= a[n - 1] {
            prev_idx
        } else {
            n - 1
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn min(a: Vec<i8>) -> (result: i8)
    requires a.len() > 0,
    ensures 
        exists|i: int| 0 <= i < a@.len() && result as int == a@[i],
        forall|i: int| 0 <= i < a@.len() ==> result as int <= a@[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): use executable code with proper types */
{
    let n = a.len();
    let idx = min_index(&a, n);
    a[idx]
}
// </vc-code>


}
fn main() {}