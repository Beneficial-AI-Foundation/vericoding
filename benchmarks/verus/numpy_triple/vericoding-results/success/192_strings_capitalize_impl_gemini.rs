// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn loop_invariant(i: int, a_seq: Seq<String>, result_seq: Seq<String>) -> bool {
    &&& i <= a_seq.len()
    &&& result_seq.len() == i
    &&& (forall|j: int| 0 <= j < i ==> #[trigger] result_seq[j]@.len() == a_seq[j]@.len())
}
// </vc-helpers>

// <vc-spec>
fn capitalize(a: Vec<String>) -> (result: Vec<String>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] result[i]@.len() == a[i]@.len()
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            loop_invariant(i as int, a@, result@),
        decreases a.len() - i,
    {
        let s_clone = a[i].clone();
        result.push(s_clone);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}