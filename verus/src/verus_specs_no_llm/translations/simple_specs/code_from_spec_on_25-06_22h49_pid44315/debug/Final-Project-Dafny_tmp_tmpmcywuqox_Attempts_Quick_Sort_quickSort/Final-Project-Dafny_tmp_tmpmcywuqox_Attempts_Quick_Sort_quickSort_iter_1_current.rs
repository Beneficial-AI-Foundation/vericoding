use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn threshold(thres: int, seq: Seq<int>) -> (seq_1: Seq<int>, seq_2: Seq<int>)
    ensures
        (forall|x: int| seq_1.contains(x) ==> x <= thres),
        (forall|x: int| seq_2.contains(x) ==> x >= thres),
        seq_1.len() + seq_2.len() == seq.len(),
        seq_1.to_multiset().add(seq_2.to_multiset()) == seq.to_multiset(),
{
    let mut seq_1: Seq<int> = Seq::empty();
    let mut seq_2: Seq<int> = Seq::empty();
    let mut i = 0;
    
    while i < seq.len()
        invariant
            0 <= i <= seq.len(),
            (forall|x: int| seq_1.contains(x) ==> x <= thres),
            (forall|x: int| seq_2.contains(x) ==> x >= thres),
            seq_1.len() + seq_2.len() == i,
            seq_1.to_multiset().add(seq_2.to_multiset()) == seq.subrange(0, i as int).to_multiset(),
    {
        let val = seq[i as int];
        if val <= thres {
            seq_1 = seq_1.push(val);
        } else {
            seq_2 = seq_2.push(val);
        }
        i = i + 1;
    }
    
    (seq_1, seq_2)
}

fn quick_sort(seq: Seq<int>) -> (seq_sorted: Seq<int>)
    ensures
        seq_sorted.to_multiset() == seq.to_multiset(),
        forall|i: int, j: int| 0 <= i < j < seq_sorted.len() ==> seq_sorted[i] <= seq_sorted[j],
    decreases seq.len()
{
    if seq.len() <= 1 {
        seq
    } else {
        let pivot = seq[0];
        let rest = seq.subrange(1, seq.len() as int);
        let (smaller, larger) = threshold(pivot, rest);
        
        let sorted_smaller = quick_sort(smaller);
        let sorted_larger = quick_sort(larger);
        
        seq![pivot].add(sorted_smaller).add(sorted_larger)
    }
}

}