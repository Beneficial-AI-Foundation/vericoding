use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn seq_equal(s1: Seq<int>, s2: Seq<int>) -> bool {
    s1 == s2
}
// </vc-helpers>

// <vc-spec>
fn contains_sequence(list: Seq<Seq<int>>, sub: Seq<int>) -> (result: bool)
    ensures result <==> exists|i: int| 0 <= i < list.len() && sub == list[i]
// </vc-spec>
// <vc-code>
{
    let mut idx: usize = 0;
    while idx < list.len()
        invariant
            0 <= idx <= list.len(),
            forall|j: int| 0 <= j < idx ==> sub != list[j],
    {
        if sub == list[idx as int] {
            assert(0 <= idx as int && idx as int < list.len());
            assert(sub == list[idx as int]);
            return true;
        }
        idx = idx + 1;
    }
    
    assert(idx == list.len());
    assert(forall|j: int| 0 <= j < list.len() ==> sub != list[j]);
    false
}
// </vc-code>

fn main() {
}

}