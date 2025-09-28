use vstd::prelude::*;

verus! {

spec fn quick_sorted(seq: Seq<int>) -> bool {
    forall|idx_1: int, idx_2: int| 0 <= idx_1 < idx_2 < seq.len() ==> seq[idx_1] <= seq[idx_2]
}

// <vc-helpers>
/* Updated helpers: none required beyond vstd::prelude imports */
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
    let mut processed: Seq<int> = Seq::empty();
    let mut i: int = 0;
    while i < seq.len()
        invariant
            0 <= i,
            i <= seq.len(),
            left.len() + right.len() == i,
            processed.len() == i,
            forall|x: int| left.contains(x) ==> x <= thres,
            forall|x: int| right.contains(x) ==> x >= thres,
            processed.to_multiset() == left.to_multiset().add(right.to_multiset()),
            forall|j: int| 0 <= j && j < i ==> processed[j] == seq[j]
    {
        let x: int = seq[i];
        processed = processed.push(x);
        if x <= thres {
            left = left.push(x);
        } else {
            right = right.push(x);
        }
        i = i + 1;
    }
    let res_left: Seq<int> = left;
    let res_right: Seq<int> = right;
    proof {
        assert(i == seq.len());
        assert(processed.len() == seq.len());
        assert(forall|j: int| 0 <= j && j < seq.len() ==> processed[j] == seq[j]);
        assert(processed == seq);
        assert(processed.to_multiset() == res_left.to_multiset().add(res_right.to_multiset()));
        assert(res_left.to_multiset().add(res_right.to_multiset()) == seq.to_multiset());
    }
    (res_left, res_right)
}
// </vc-code>

fn main() {
}

}