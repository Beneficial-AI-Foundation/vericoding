use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
fn contains_sequence(list: Seq<Seq<int>>, sub: Seq<int>) -> (result: bool)
    ensures result <==> exists|i: int| 0 <= i < list.len() && sub == list[i]
// </vc-spec>
// <vc-code>
{
    return exists |j: nat| j < list.len() && sub == list[j];
}
// </vc-code>

fn main() {
}

}