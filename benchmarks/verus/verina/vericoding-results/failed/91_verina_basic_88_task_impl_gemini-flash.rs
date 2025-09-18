// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): empty, no helpers */
// </vc-helpers>

// <vc-spec>
fn to_array(xs: &Seq<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == xs.len(),
        forall|i: int| 0 <= i < xs.len() ==> result[i] == xs[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Corrected type mismatches (int vs. nat) for loop index `i` and `xs.len()`, and allowed `Vec` indexing using the `@` operator. */
    let mut v: Vec<i32> = Vec::new();
    let mut i: int = 0;
    while i < xs.len() as int
        invariant
            v.len() as int == i,
            forall|j: int| 0 <= j < i ==> v@[j as int] == xs@[j as nat],
            0 <= i <= xs.len() as int,
        decreases xs.len() as int - i
    {
        v.push(xs@[i as nat]);
        i = i + 1;
    }
    v
}
// </vc-code>

}
fn main() {}