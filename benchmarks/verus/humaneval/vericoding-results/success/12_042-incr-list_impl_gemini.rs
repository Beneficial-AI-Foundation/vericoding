// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn incr_list(l: Vec<i32>) -> (result: Vec<i32>)

    requires
        forall|i: int| 0 <= i < l.len() ==> l[i] + 1 <= i32::MAX,

    ensures
        result.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> #[trigger] result[i] == l[i] + 1,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): added precondition to invariant and an assertion for the new element */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < l.len()
        invariant
            0 <= i <= l.len(),
            result.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> result[j] == l[j] + 1,
            forall|k: int| 0 <= k < l.len() ==> l[k] + 1 <= i32::MAX,
        decreases l.len() - i
    {
        result.push(l[i] + 1);
        assert(result[i as int] == l[i as int] + 1);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}