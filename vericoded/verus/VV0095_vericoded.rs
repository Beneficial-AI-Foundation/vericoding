// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn contains_consecutive_numbers(a: &Vec<i32>) -> (result: bool)
    ensures
        result <==> exists|i: int| {
            &&& 0 <= i < a.len() - 1
            &&& #[trigger] a[i] + 1 == a[(i + 1) as int]
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): restructured loop to avoid overflow and indexing errors */
    if a.len() < 2 {
        return false;
    }

    let mut i: usize = 0;
    while i < a.len() - 1
        invariant
            a.len() >= 2,
            0 <= i <= a.len() - 1,
            forall|j: int| 0 <= j < (i as int) ==> #[trigger] (a[j] as int) + 1 != (a[j + 1] as int),
        decreases (a.len() - 1) - i,
    {
        if a[i] < i32::MAX && a[i] + 1 == a[i + 1] {
            return true;
        }
        i = i + 1;
    }

    return false;
}
// </vc-code>

}
fn main() {}