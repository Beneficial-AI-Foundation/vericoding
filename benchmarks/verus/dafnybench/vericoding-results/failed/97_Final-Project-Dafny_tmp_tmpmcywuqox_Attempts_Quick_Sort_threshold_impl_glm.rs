use vstd::prelude::*;

verus! {

spec fn quick_sorted(seq: Seq<int>) -> bool {
    forall|idx_1: int, idx_2: int| 0 <= idx_1 < idx_2 < seq.len() ==> seq[idx_1] <= seq[idx_2]
}

// <vc-helpers>
impl SeqHelper for Seq<int> {
    spec fn to_multiset(self) -> vstd::multiset::Multiset<int> {
        vstd::multiset::Multiset::from_seq(self)
    }
}

trait SeqHelper {
    spec fn to_multiset(self) -> vstd::multiset::Multiset<int>;
}

impl MultisetHelper for vstd::multiset::Multiset<int> {
    closed spec fn add(self, other: vstd::multiset::Multiset<int>) -> vstd::multiset::Multiset<int> {
        self.union(other)
    }
}

trait MultisetHelper {
    closed spec fn add(self, other: vstd::multiset::Multiset<int>) -> vstd::multiset::Multiset<int>;
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
    let n = seq.len();
    let mut i: nat = 0;
    while i < n
        invariant 
            i <= n,
            left.len() + right.len() == i,
            left.to_multiset().add(right.to_multiset()) == seq.subrange(0, i as int).to_multiset(),
            (forall|j: int| 0 <= j < left.len() ==> left[j] <= thres),
            (forall|j: int| 0 <= j < right.len() ==> right[j] >= thres)
    {
        let x = seq[i];
        if x <= thres {
            left = left.push(x);
        } else {
            right = right.push(x);
        }
        i += 1;
    }
    (left, right)
}
// </vc-code>

fn main() {
}

}