// ATOM 
pub open spec fn quickSorted(Seq: Seq<int>) -> bool
{
    forall|idx_1: int, idx_2: int| 0 <= idx_1 < idx_2 < Seq.len() ==> Seq[idx_1] <= Seq[idx_2]
}

// SPEC 
pub fn threshold(thres: int, Seq: Seq<int>) -> (Seq_1: Seq<int>, Seq_2: Seq<int>)
    ensures
        (forall|x: int| Seq_1.contains(x) ==> x <= thres) && (forall|x: int| Seq_2.contains(x) ==> x >= thres),
        Seq_1.len() + Seq_2.len() == Seq.len(),
        Seq_1.to_multiset() + Seq_2.to_multiset() == Seq.to_multiset(),
{
}

// ATOM 
proof fn Lemma_1(Seq_1: Seq<int>, Seq_2: Seq<int>)
    requires
        Seq_1.to_multiset() == Seq_2.to_multiset(),
    ensures
        forall|x: int| Seq_1.contains(x) ==> Seq_2.contains(x),
{
}

// SPEC 
pub fn quickSort(Seq: Seq<int>) -> (Seq_prime: Seq<int>)
    ensures
        Seq.to_multiset() == Seq_prime.to_multiset(),
{
}