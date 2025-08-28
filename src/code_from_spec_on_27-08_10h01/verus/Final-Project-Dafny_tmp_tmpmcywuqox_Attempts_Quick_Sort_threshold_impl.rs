use vstd::prelude::*;

verus! {

spec fn quick_sorted(seq: Seq<int>) -> bool {
    forall|idx_1: int, idx_2: int| 0 <= idx_1 < idx_2 < seq.len() ==> seq[idx_1] <= seq[idx_2]
}

// <vc-helpers>
ghost fn lemma_multiset_property(seq: Seq<int>, left: Seq<int>, right: Seq<int>, i: int)
    requires
        0 <= i <= seq.len(),
        left.to_multiset().add(right.to_multiset()) == seq.subrange(0, i).to_multiset()
    ensures
        i == seq.len() ==> left.to_multiset().add(right.to_multiset()) == seq.to_multiset()
{
    if i == seq.len() {
        assert(seq.subrange(0, i) == seq);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn threshold(thres: int, seq: Seq<int>) -> (ret: (Seq<int>, Seq<int>))
    ensures 
        (forall|x: int| ret.0.contains(x) ==> x <= thres) &&
        (forall|x: int| ret.1.contains(x) ==> x >= thres) &&
        ret.0.len() + ret.1.len() == seq.len() &&
        ret.0.to_multiset().add(ret.1.to_multiset()) == seq.to_multiset()
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut left: Vec<int> = Vec::new();
    let mut right: Vec<int> = Vec::new();
    
    let mut i: usize = 0;
    while i < seq.len()
        invariant
            0 <= i <= seq.len(),
            forall|x: int| left@.contains(x) ==> x <= thres,
            forall|x: int| right@.contains(x) ==> x >= thres,
            left@.to_multiset().add(right@.to_multiset()) == seq.subrange(0, i as int).to_multiset()
    {
        let ghost elem_ghost = seq[i as int];
        let elem = elem_ghost;
        if elem <= thres {
            left.push(elem);
        } else {
            right.push(elem);
        }
        i += 1;
    }
    
    proof {
        lemma_multiset_property(seq, left@, right@, i as int);
    }
    
    (left@, right@)
}
// </vc-code>

fn main() {
}

}