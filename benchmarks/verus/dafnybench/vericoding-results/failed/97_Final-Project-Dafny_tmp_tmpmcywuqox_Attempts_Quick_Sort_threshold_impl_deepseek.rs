use vstd::prelude::*;

verus! {

spec fn quick_sorted(seq: Seq<int>) -> bool {
    forall|idx_1: int, idx_2: int| 0 <= idx_1 < idx_2 < seq.len() ==> seq[idx_1] <= seq[idx_2]
}

// <vc-helpers>
spec fn filter_le(seq: Seq<int>, thres: int) -> (s: Seq<int>)
    ensures 
        forall|x: int| s.contains(x) ==> x <= thres,
        forall|i: int| 0 <= i < s.len() ==> s.index(i) <= thres,
    decreases seq.len(),
{
    if seq.len() == 0 {
        Seq::empty()
    } else {
        let first = seq[0];
        let rest = filter_le(seq.subrange(1, seq.len() as int), thres);
        if first <= thres {
            rest.insert(0, first)
        } else {
            rest
        }
    }
}

spec fn filter_ge(seq: Seq<int>, thres: int) -> (s: Seq<int>)
    ensures 
        forall|x: int| s.contains(x) ==> x >= thres,
        forall|i: int| 0 <= i < s.len() ==> s.index(i) >= thres,
    decreases seq.len(),
{
    if seq.len() == 0 {
        Seq::empty()
    } else {
        let first = seq[0];
        let rest = filter_ge(seq.subrange(1, seq.len() as int), thres);
        if first >= thres {
            rest.insert(0, first)
        } else {
            rest
        }
    }
}

proof fn filter_le_len(seq: Seq<int>, thres: int)
    ensures
        filter_le(seq, thres).len() <= seq.len(),
    decreases seq.len(),
{
    if seq.len() > 0 {
        filter_le_len(seq.subrange(1, seq.len() as int), thres);
    }
}

proof fn filter_ge_len(seq: Seq<int>, thres: int)
    ensures
        filter_ge(seq, thres).len() <= seq.len(),
    decreases seq.len(),
{
    if seq.len() > 0 {
        filter_ge_len(seq.subrange(1, seq.len() as int), thres);
    }
}

proof fn filter_le_multiset(seq: Seq<int>, thres: int)
    ensures
        filter_le(seq, thres).to_multiset().add(filter_ge(seq, thres).to_multiset()) == seq.to_multiset(),
    decreases seq.len(),
{
    if seq.len() > 0 {
        filter_le_multiset(seq.subrange(1, seq.len() as int), thres);
    }
}

proof fn filter_le_property(seq: Seq<int>, thres: int)
    ensures
        forall|x: int| filter_le(seq, thres).contains(x) ==> x <= thres,
    decreases seq.len(),
{
    if seq.len() > 0 {
        filter_le_property(seq.subrange(1, seq.len() as int), thres);
    }
}

proof fn filter_ge_property(seq: Seq<int>, thres: int)
    ensures
        forall|x: int| filter_ge(seq, thres).contains(x) ==> x >= thres,
    decreases seq.len(),
{
    if seq.len() > 0 {
        filter_ge_property(seq.subrange(1, seq.len() as int), thres);
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
    let mut left: Vec<int> = Vec::new();
    let mut right: Vec<int> = Vec::new();
    
    let mut i: usize = 0;
    while i < seq.len() as usize
        invariant
            0 <= i <= seq.len() as usize,
            forall|j: int| 0 <= j < left@.len() ==> left@[j as nat] <= thres,
            forall|j: int| 0 <= j < right@.len() ==> right@[j as nat] >= thres,
            left@.len() + right@.len() == i as nat,
            left@.to_multiset().add(right@.to_multiset()) == seq.subrange(0, i as int).to_multiset(),
    {
        let idx = i as int;
        let elem = seq[idx];
        if elem <= thres {
            proof {
                assert(forall|j: int| 0 <= j < left@.len() ==> left@[j as nat] <= thres);
            }
            left.push(elem);
            proof {
                assert(forall|j: int| 0 <= j < left@.len() ==> left@[j as nat] <= thres);
                assert(left@[left@.len() - 1] == elem);
                assert(left@.to_multiset() == old(left)@.to_multiset().insert(elem));
            }
        } else {
            proof {
                assert(forall|j: int| 0 <= j < right@.len() ==> right@[j as nat] >= thres);
            }
            right.push(elem);
            proof {
                assert(forall|j: int| 0 <= j < right@.len() ==> right@[j as nat] >= thres);
                assert(right@[right@.len() - 1] == elem);
                assert(right@.to_multiset() == old(right)@.to_multiset().insert(elem));
            }
        }
        i = i + 1;
    }
    
    proof {
        filter_le_property(seq, thres);
        filter_ge_property(seq, thres);
        filter_le_multiset(seq, thres);
        assert(seq.subrange(0, seq.len() as int) == seq);
        assert(left@.to_multiset().add(right@.to_multiset()) == seq.to_multiset());
    }
    
    (left.into(), right.into())
}
// </vc-code>

fn main() {
}

}