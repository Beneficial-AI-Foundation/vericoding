// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn linear_search(a: &Vec<i32>, e: i32) -> (result: usize)
    ensures
        result <= a.len(),
        result == a.len() || a[result as int] == e,
        forall|i: int| 0 <= i < result ==> a[i] != e,
// </vc-spec>
// <vc-code>
{ /* code modified by LLM (iteration 3): Added decreases clause to the while loop and fixed potential integer overflow for loop variable `i` */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|j: int| 0 <= j < i ==> a[j] != e,
        decreases a.len() - i
    {
        if a[i] == e {
            return i;
        }
        i = i + 1;
    }
    a.len()
}
// </vc-code>

}
fn main() {}