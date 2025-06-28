// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn threshold(thres: int, Seq: Seq<int>) -> (Seq_1: Seq<int>, Seq_2: Seq<int>)
    ensures
        (forall|x| Seq_1.contains(x) ==> x <= thres) && (forall|x| Seq_2.contains(x) ==> x >= thres),
        Seq_1.len() + Seq_2.len() == Seq.len(),
        multiset(Seq_1) + multiset(Seq_2) == multiset(Seq)
{
    let mut seq_1 = Seq::empty();
    let mut seq_2 = Seq::empty();
    let mut i = 0;
    
    while i < Seq.len()
        invariant
            0 <= i <= Seq.len(),
            (forall|x| seq_1.contains(x) ==> x <= thres),
            (forall|x| seq_2.contains(x) ==> x >= thres),
            seq_1.len() + seq_2.len() == i,
            multiset(seq_1) + multiset(seq_2) == multiset(Seq.subrange(0, i as int))
    {
        let elem = Seq[i as int];
        if elem <= thres {
            seq_1 = seq_1.push(elem);
        } else {
            seq_2 = seq_2.push(elem);
        }
        i = i + 1;
    }
    
    (seq_1, seq_2)
}

}