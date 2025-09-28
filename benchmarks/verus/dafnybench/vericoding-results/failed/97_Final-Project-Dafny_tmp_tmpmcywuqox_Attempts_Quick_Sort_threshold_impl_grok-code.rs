use vstd::prelude::*;

verus! {

spec fn quick_sorted(seq: Seq<int>) -> bool {
    forall|idx_1: int, idx_2: int| 0 <= idx_1 < idx_2 < seq.len() ==> seq[idx_1] <= seq[idx_2]
}

// <vc-helpers>

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
    let mut left: Vec<int> = Vec::new();
    let mut right: Vec<int> = Vec::new();
    let mut i: nat = 0;
    while i < seq@.len()
        invariant
            i <= seq@.len(),
            left@.len() + right@.len() == i,
            left.view().to_multiset().add(right.view().to_multiset()) == seq@.take(i as int).to_multiset(),
            forall|x: int| left.view().contains(x) ==> (x <= thres),
            forall|x: int| right.view().contains(x) ==> (x >= thres)
        decreases seq@.len() - i
    {
        assert(i < seq@.len());
        let val = seq[i];
        if val <= thres {
            left.push(val);
        } else {
            right.push(val);
        }
        i = i + 1;
    }
    (left.view(), right.view())
}
// </vc-code>

fn main() {
}

}