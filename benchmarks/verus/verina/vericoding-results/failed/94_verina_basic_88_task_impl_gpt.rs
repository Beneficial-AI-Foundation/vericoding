// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): retained simple index-range predicate for potential invariants */
spec fn is_valid_index(i: int, len: int) -> bool { 0 <= i && i < len }
// </vc-helpers>

// <vc-spec>
fn to_array(xs: &Seq<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == xs.len(),
        forall|i: int| 0 <= i < xs.len() ==> result[i] == xs[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use fully-qualified vstd Vec::from_seq to convert Seq into Vec with matching view */
    let v: Vec<i32> = vstd::vec::Vec::<i32>::from_seq(xs.clone());
    v
}
// </vc-code>

}
fn main() {}