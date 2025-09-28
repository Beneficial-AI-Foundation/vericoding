// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers are needed for this implementation. */
// </vc-helpers>

// <vc-spec>
#[verifier::exec_allows_no_decreases_clause]
fn insert_before_each(s: Seq<String>, x: String) -> (v: Seq<String>)
    ensures
        v.len() == 2 * s.len(),
        forall|i: int| 0 <= i < s.len() ==> v[2*i] == x && v[2*i + 1] == s[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): switched loop counter to usize to resolve compilation errors */
    let mut v: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            v.view().len() == (2 * i) as nat,
            forall|j: int| 0 <= j < (i as int) ==> v.view()@[2*j] == x && v.view()@[2*j + 1] == s@[j],
        decreases s.len() - i,
    {
        v.push(x.clone());
        v.push(s[i].clone());
        i = i + 1;
    }
    v.into()
}
// </vc-code>

}
fn main() {}