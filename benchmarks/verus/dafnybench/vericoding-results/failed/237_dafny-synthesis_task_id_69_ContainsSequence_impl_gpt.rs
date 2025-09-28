use vstd::prelude::*;

verus! {

// <vc-helpers>
pub open spec fn contains_helper(list: Seq<Seq<int>>, sub: Seq<int>) -> bool {
    exists|i: int| 0 <= i < list.len() && sub == list[i]
}

proof fn lemma_contains_equiv(list: Seq<Seq<int>>, sub: Seq<int>)
    ensures contains_helper(list, sub) <==> exists|i: int| 0 <= i < list.len() && sub == list[i]
{
    reveal(contains_helper);
}
// </vc-helpers>

// <vc-spec>
fn contains_sequence(list: Seq<Seq<int>>, sub: Seq<int>) -> (result: bool)
    ensures result <==> exists|i: int| 0 <= i < list.len() && sub == list[i]
// </vc-spec>
// <vc-code>
{
    exists|i: int| 0 <= i < list.len() && sub == list[i]
}
// </vc-code>

fn main() {
}

}