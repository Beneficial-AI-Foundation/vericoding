// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers needed for linear search. */
// </vc-helpers>

// <vc-spec>
fn linear_search(a: &Vec<i32>, e: i32) -> (result: usize)
    requires exists|i: int| 0 <= i < a.len() && a[i] == e,
    ensures
        result < a.len(),
        a[result as int] == e,
        forall|k: int| 0 <= k < result ==> a[k] != e,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Implement linear search with a while loop to find the first occurrence and satisfy postconditions. */
    let mut i: usize = 0;
    let mut found: bool = false;
    let mut result: usize = 0; // Default, but will be set
    while i < a.len() {
        if a[i] == e {
            found = true;
            result = i;
            break;
        }
        i = i + 1;
    }
    // Since pre ensures exists, this will find it
    assert(found); // Redundant but helps verification
    result
}
// </vc-code>

}
fn main() {}