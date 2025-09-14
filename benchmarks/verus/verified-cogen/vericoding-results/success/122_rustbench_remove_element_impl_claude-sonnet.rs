// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn remove_element(a: &[i32], pos: usize) -> (result: Vec<i32>)
    requires
        0 <= pos < a.len(),
    ensures
        result.len() == a.len() - 1,
        forall|i: int| 0 <= i < pos ==> result[i] == a[i],
        forall|i: int| pos <= i < result.len() ==> result[i] == a[i + 1],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added missing decreases clause */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == if i <= pos { i as int } else { (i - 1) as int },
            forall|j: int| 0 <= j < result.len() && j < pos ==> result[j] == a[j],
            forall|j: int| 0 <= j < result.len() && j >= pos ==> result[j] == a[j + 1],
        decreases a.len() - i
    {
        if i != pos {
            result.push(a[i]);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}