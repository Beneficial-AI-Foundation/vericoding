// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prefix non-equality predicate using int indices for specification */
spec fn prefix_neq(a: &Vec<i32>, i: int, key: i32) -> bool { forall|j: int| 0 <= j && j < i ==> a@[j] != key }
// </vc-helpers>

// <vc-spec>
fn find(a: &Vec<i32>, key: i32) -> (result: i32)
    ensures
        (result == -1 || (result >= 0 && result < a.len())),
        result != -1 ==> (a[result as int] == key && forall|i: int| 0 <= i < result ==> a[i] != key),
        result == -1 ==> forall|i: int| 0 <= i < a.len() ==> a[i] != key,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate with usize index and use a@[i] indexing and prefix_neq (with i cast to int in invariants) */
    let n: usize = a.len();
    let mut i: usize = 0;
    while i < n
        invariant i <= n
        invariant prefix_neq(a, i as int, key)
        decreases n - i
    {
        if a[i] == key {
            return i as i32;
        } else {
            i = i + 1;
        }
    }
    -1
}
// </vc-code>

}
fn main() {}