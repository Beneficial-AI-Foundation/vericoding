// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): define sequence from a spec iterator using usize length to avoid nat in exec code */
spec fn seq_of_iter<T>(n: usize, iter: spec_fn(usize) -> T) -> Seq<T> {
    Seq::new(n as nat, |i: int| iter(i as usize))
}
// </vc-helpers>

// <vc-spec>
fn fromiter<T: Copy>(n: usize, iter: spec_fn(usize) -> T) -> (result: Vec<T>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i] == iter(i as usize)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): construct vector from a ghost sequence without using nat in exec context */
    let ghost s = seq_of_iter(n, iter);
    let v: Vec<T> = Vec::from_seq(s);
    v
}
// </vc-code>

}
fn main() {}