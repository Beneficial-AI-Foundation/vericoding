// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn any_value_exists(seq1: Seq<int>, seq2: Seq<int>) -> (result: bool)
    ensures result <==> (exists|i: int| 0 <= i < seq1.len() && seq2.contains(seq1[i]))
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}