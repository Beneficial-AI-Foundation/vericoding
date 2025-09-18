// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Add decreases clause helper */
fn ones_like_helper<T>(a: &Vec<T>, i: int) -> (result: bool)
    ensures
        result == true,
{
    true
}

proof fn ones_like_lemma<T>(a: &Vec<T>, i: int)
    requires
        0 <= i < a.len(),
    ensures
        true,
{
}
// </vc-helpers>

// <vc-spec>
fn ones_like<T>(a: &Vec<T>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == 1,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Add decreases clause to while loop */
{
    let mut result = Vec::new();
    let mut j = 0;
    while j < a.len()
        invariant
            result.len() == j,
            forall|k: int| 0 <= k < j ==> result[k] == 1,
            j <= a.len(),
        decreases a.len() - j,
    {
        result.push(1);
        j = j + 1;
    }
    result
}
// </vc-code>

}
fn main() {}