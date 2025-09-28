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
    let mut i: usize = 0;
    while i < list.len()
        invariant
            0 <= i <= list.len(),
            forall|j: int| 0 <= j < i ==> sub != list[j]
    {
        if sub == list[i as int] {
            assert(0 <= i < list.len() && sub == list[i as int]);
            return true;
        }
        i = i + 1;
    }
    assert(forall|j: int| 0 <= j < list.len() ==> sub != list[j]);
    false
}
// </vc-code>

fn main() {
}

}