use vstd::prelude::*;

verus! {

spec fn quick_sorted(seq: Seq<int>) -> bool {
    forall|idx_1: int, idx_2: int| 0 <= idx_1 < idx_2 < seq.len() ==> seq[idx_1] <= seq[idx_2]
}

// <vc-helpers>
// Helper lemma to prove multiset properties during iteration
proof fn multiset_push_distributes(s1: Seq<int>, s2: Seq<int>, v: int)
    ensures
        s1.push(v).to_multiset() =~= s1.to_multiset().insert(v),
        s1.push(v).to_multiset().add(s2.to_multiset()) =~= s1.to_multiset().insert(v).add(s2.to_multiset()),
{
    assert(s1.push(v).to_multiset() =~= s1.to_multiset().insert(v));
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
    let mut low: Vec<int> = Vec::new();
    let mut high: Vec<int> = Vec::new();
    let mut i: usize = 0;
    
    while i < seq.len()
        invariant
            i <= seq.len(),
            forall|x: int| low@.contains(x) ==> x <= thres,
            forall|x: int| high@.contains(x) ==> x >= thres,
            low@.len() + high@.len() == i as int,
            low@.to_multiset().add(high@.to_multiset()) =~= seq.subrange(0, i as int).to_multiset(),
    {
        let val: int = seq[i as int];
        
        if val <= thres {
            proof {
                multiset_push_distributes(low@, high@, val);
                assert(seq.subrange(0, i as int + 1) =~= seq.subrange(0, i as int).push(val));
            }
            low.push(val);
        } else {
            proof {
                multiset_push_distributes(high@, low@, val);
                assert(seq.subrange(0, i as int + 1) =~= seq.subrange(0, i as int).push(val));
            }
            high.push(val);
        }
        
        i = i + 1;
    }
    
    proof {
        assert(seq.subrange(0, seq.len() as int) =~= seq);
    }
    
    (low@, high@)
}
// </vc-code>

fn main() {
}

}