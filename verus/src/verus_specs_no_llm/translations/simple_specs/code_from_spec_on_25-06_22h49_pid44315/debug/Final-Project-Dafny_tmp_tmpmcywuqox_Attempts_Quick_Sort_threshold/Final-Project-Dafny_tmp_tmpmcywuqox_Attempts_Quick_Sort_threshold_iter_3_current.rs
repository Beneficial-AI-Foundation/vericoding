use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn threshold(thres: int, Seq: Seq<int>) -> (Seq_1: Seq<int>, Seq_2: Seq<int>)
    ensures
        (forall|x: int| Seq_1.contains(x) ==> x <= thres) && (forall|x: int| Seq_2.contains(x) ==> x >= thres),
        Seq_1.len() + Seq_2.len() == Seq.len(),
        Seq_1.to_multiset() + Seq_2.to_multiset() == Seq.to_multiset()
{
    let mut seq_1 = Seq::empty();
    let mut seq_2 = Seq::empty();
    let mut i = 0;
    
    while i < Seq.len()
        invariant
            0 <= i <= Seq.len(),
            (forall|x: int| seq_1.contains(x) ==> x <= thres),
            (forall|x: int| seq_2.contains(x) ==> x >= thres),
            seq_1.len() + seq_2.len() == i,
            seq_1.to_multiset() + seq_2.to_multiset() == Seq.subrange(0, i as int).to_multiset()
    {
        let elem = Seq[i as int];
        if elem <= thres {
            seq_1 = seq_1.push(elem);
            if elem == thres {
                seq_2 = seq_2.push(elem);
            }
        } else {
            seq_2 = seq_2.push(elem);
        }
        i = i + 1;
        
        // Proof assertions to help with multiset reasoning
        proof {
            let old_subrange = Seq.subrange(0, (i - 1) as int);
            let new_subrange = Seq.subrange(0, i as int);
            assert(new_subrange == old_subrange.push(elem));
            assert(new_subrange.to_multiset() == old_subrange.to_multiset().insert(elem));
        }
    }
    
    // Final proof assertion
    proof {
        assert(Seq.subrange(0, Seq.len() as int) == Seq);
    }
    
    (seq_1, seq_2)
}

}