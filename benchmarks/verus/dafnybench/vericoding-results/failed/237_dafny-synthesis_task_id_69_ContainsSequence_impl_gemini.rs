// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn contains_sequence_rec(list: Seq<Seq<int>>, sub: Seq<int>, i: int) -> (result: bool)
    requires
        0 <= i <= list.len(),
    ensures
        result <==> (exists|k: int| i <= k < list.len() && sub == list[k]),
    decreases list.len() - i
{
    if i >= list.len() {
        false
    } else if list[i] == sub {
        true
    } else {
        contains_sequence_rec(list, sub, i + 1)
    }
}
// </vc-helpers>

// <vc-spec>
fn contains_sequence(list: Seq<Seq<int>>, sub: Seq<int>) -> (result: bool)
    ensures result <==> exists|i: int| 0 <= i < list.len() && sub == list[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Cast the integer literal `0` to type `int` to fix the compilation error. */
{
    contains_sequence_rec(list, sub, 0 as int)
}
// </vc-code>

}
fn main() {}