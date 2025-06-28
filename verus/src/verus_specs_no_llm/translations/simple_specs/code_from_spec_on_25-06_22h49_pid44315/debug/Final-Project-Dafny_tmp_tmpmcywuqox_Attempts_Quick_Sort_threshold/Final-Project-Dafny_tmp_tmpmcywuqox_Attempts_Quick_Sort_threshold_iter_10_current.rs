use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn threshold(thres: int, seq: Seq<int>) -> (Seq_1: Seq<int>, Seq_2: Seq<int>)
    ensures
        (forall|x: int| Seq_1.contains(x) ==> x < thres) && (forall|x: int| Seq_2.contains(x) ==> x >= thres),
        Seq_1.len() + Seq_2.len() == seq.len(),
        Seq_1.to_multiset() + Seq_2.to_multiset() == seq.to_multiset()
{
    let mut seq_1 = Seq::empty();
    let mut seq_2 = Seq::empty();
    let mut i = 0;
    
    while i < seq.len()
        invariant
            0 <= i <= seq.len(),
            (forall|x: int| seq_1.contains(x) ==> x < thres),
            (forall|x: int| seq_2.contains(x) ==> x >= thres),
            seq_1.len() + seq_2.len() == i,
            seq_1.to_multiset() + seq_2.to_multiset() == seq.subrange(0, i as int).to_multiset()
    {
        let elem = seq[i as int];
        if elem < thres {
            seq_1 = seq_1.push(elem);
        } else {
            seq_2 = seq_2.push(elem);
        }
        i = i + 1;
    }
    
    assert(seq.subrange(0, seq.len() as int) =~= seq);
    
    (seq_1, seq_2)
}

}