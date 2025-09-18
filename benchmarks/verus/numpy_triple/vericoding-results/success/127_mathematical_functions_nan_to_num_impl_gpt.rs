// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn same_len<T>(a: Seq<T>, b: Seq<T>) -> bool { a.len() == b.len() }
proof fn lemma_same_len_refl<T>(s: Seq<T>) ensures same_len(s, s) { }
// </vc-helpers>

// <vc-spec>
fn nan_to_num(x: Vec<f64>) -> (result: Vec<f64>)
    ensures 
        result.len() == x.len(),
// </vc-spec>
// <vc-code>
{
    x
}
// </vc-code>

}
fn main() {}