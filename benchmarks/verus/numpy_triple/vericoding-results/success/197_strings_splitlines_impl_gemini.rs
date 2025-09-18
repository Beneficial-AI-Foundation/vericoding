// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn create_inner_vec(s: String) -> (v: Vec<String>)
    ensures
        v.view() === seq![s],
{
    let mut v = Vec::new();
    v.push(s);
    v
}
// </vc-helpers>

// <vc-spec>
fn splitlines(a: Vec<String>, keepends: bool) -> (result: Vec<Vec<String>>)
    requires a.len() > 0,
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() >= 1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Added decreases clause to prove loop termination. */
    let mut result: Vec<Vec<String>> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> #[trigger] result.view()[j].len() >= 1
        decreases a.len() - i
    {
        let inner_vec = create_inner_vec(a[i].clone());
        result.push(inner_vec);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}