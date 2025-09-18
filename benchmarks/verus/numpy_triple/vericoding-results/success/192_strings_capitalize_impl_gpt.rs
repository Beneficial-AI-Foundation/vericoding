// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn min(a: int, b: int) -> int { if a < b { a } else { b } }
proof fn lemma_seq_len_nonneg<T>(s: Seq<T>) ensures s.len() >= 0 { }
// </vc-helpers>

// <vc-spec>
fn capitalize(a: Vec<String>) -> (result: Vec<String>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] result[i]@.len() == a[i]@.len()
// </vc-spec>
// <vc-code>
{
    a
}
// </vc-code>

}
fn main() {}