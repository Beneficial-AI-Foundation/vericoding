use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn contains_sequence(list: Seq<Seq<int>>, sub: Seq<int>) -> (result: bool)
    ensures result <==> exists|i: int| 0 <= i < list.len() && sub == list[i]
// </vc-spec>
// <vc-code>
{
    let mut i: int = 0;
    while i < list.len() {
        invariant 0 <= i <= list.len();
        invariant forall|j: int| 0 <= j < i ==> list@[j] != sub;
        if list@[i] == sub {
            return true;
        }
        i += 1;
    }
    false
}
// </vc-code>

fn main() {
}

}