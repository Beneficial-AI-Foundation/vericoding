use vstd::prelude::*;

verus! {

spec fn quick_sorted(seq: Seq<int>) -> bool {
    forall|idx_1: int, idx_2: int| 0 <= idx_1 < idx_2 < seq.len() ==> seq[idx_1] <= seq[idx_2]
}

// <vc-helpers>
spec fn partition_invariant(seq: Seq<int>, thres: int, left: Seq<int>, right: Seq<int>, processed: int) -> bool {
    0 <= processed <= seq.len() &&
    (forall|x: int| left.contains(x) ==> x <= thres) &&
    (forall|x: int| right.contains(x) ==> x >= thres) &&
    left.to_multiset().add(right.to_multiset()) == seq.subrange(0, processed).to_multiset()
}

proof fn lemma_multiset_partition(seq: Seq<int>, thres: int, left: Seq<int>, right: Seq<int>, i: int, new_left: Seq<int>, new_right: Seq<int>)
    requires
        0 <= i < seq.len(),
        (forall|x: int| left.contains(x) ==> x <= thres),
        (forall|x: int| right.contains(x) ==> x >= thres),
        left.to_multiset().add(right.to_multiset()) == seq.subrange(0, i).to_multiset(),
        seq[i] <= thres ==> new_left == left.push(seq[i]) && new_right == right,
        seq[i] > thres ==> new_left == left && new_right == right.push(seq[i])
    ensures
        new_left.to_multiset().add(new_right.to_multiset()) == seq.subrange(0, i + 1).to_multiset()
{
    if seq[i] <= thres {
        assert(seq.subrange(0, i + 1) == seq.subrange(0, i).push(seq[i]));
        assert(seq.subrange(0, i + 1).to_multiset() == seq.subrange(0, i).to_multiset().add(Seq::new(1, |_| seq[i]).to_multiset()));
    } else {
        assert(seq.subrange(0, i + 1) == seq.subrange(0, i).push(seq[i]));
        assert(seq.subrange(0, i + 1).to_multiset() == seq.subrange(0, i).to_multiset().add(Seq::new(1, |_| seq[i]).to_multiset()));
    }
}
// </vc-helpers>

// <vc-spec>
fn threshold(thres: int, seq: Seq<int>) -> (ret: (Seq<int>, Seq<int>))
    ensures 
        (forall|x: int| ret.0.contains(x) ==> x <= thres) &&
        (forall|x: int| ret.1.contains(x) ==> x >= thres) &&
        ret.0.len() + ret.1.len() == seq.len() &&
        ret.0.to_multiset().add(ret.1.to_multiset()) == seq.to_multiset()
// </vc-spec>
// <vc-code>
{
    let mut left: Seq<int> = Seq::empty();
    let mut right: Seq<int> = Seq::empty();
    let mut i: usize = 0;
    
    while i < seq.len() as usize
        invariant
            0 <= i <= seq.len(),
            (forall|x: int| left.contains(x) ==> x <= thres),
            (forall|x: int| right.contains(x) ==> x >= thres),
            left.to_multiset().add(right.to_multiset()) == seq.subrange(0, i as int).to_multiset()
    {
        if seq[i as int] <= thres {
            proof {
                lemma_multiset_partition(seq, thres, left, right, i as int, left.push(seq[i as int]), right);
            }
            left = left.push(seq[i as int]);
        } else {
            proof {
                lemma_multiset_partition(seq, thres, left, right, i as int, left, right.push(seq[i as int]));
            }
            right = right.push(seq[i as int]);
        }
        i = i + 1;
    }
    
    proof {
        assert(seq.subrange(0, seq.len() as int) == seq);
    }
    
    (left, right)
}
// </vc-code>

fn main() {
}

}