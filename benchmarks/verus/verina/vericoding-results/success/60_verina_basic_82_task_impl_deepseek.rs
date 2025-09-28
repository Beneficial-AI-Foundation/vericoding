// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn remove_front_spec(a: Seq<int>) -> (result: Seq<int>)
    requires a.len() > 0,
    ensures
        result.len() == a.len() - 1,
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i + 1],
{
    /* helper modified by LLM (iteration 2): Fixed proof function syntax */
    a.subrange(1, a.len() as int)
}
// </vc-helpers>

// <vc-spec>
fn remove_front(a: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() > 0,
    ensures
        a.len() > 0,
        result.len() == a.len() - 1,
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i + 1],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed vector construction with proper indexing */
    let mut result = Vec::new();
    let mut i = 1;
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            result.len() == i - 1,
            forall|j: int| 0 <= j < result.len() ==> result[j] == a[j + 1],
        decreases a.len() - i,
    {
        result.push(a[i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}