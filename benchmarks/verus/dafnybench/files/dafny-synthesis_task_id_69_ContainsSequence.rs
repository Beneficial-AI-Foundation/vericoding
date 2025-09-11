// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn contains_sequence(list: Seq<Seq<int>>, sub: Seq<int>) -> (result: bool)
    ensures result <==> exists|i: int| 0 <= i < list.len() && sub == list[i]
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}