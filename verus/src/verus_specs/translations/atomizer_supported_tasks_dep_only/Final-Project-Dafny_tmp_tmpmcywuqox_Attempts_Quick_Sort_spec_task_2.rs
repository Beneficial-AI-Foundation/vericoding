// SPEC 

pub fn quickSort(Seq: Seq<int>) -> (Seq': Seq<int>)
    ensures(multiset(Seq) == multiset(Seq'))
{
}

// SPEC 

pub fn threshold(thres: int, Seq: Seq<int>) -> (Seq_1: Seq<int>, Seq_2: Seq<int>)
    ensures((forall|x| x in Seq_1 ==> x <= thres) && (forall|x| x in Seq_2 ==> x >= thres))
    ensures(|Seq_1| + |Seq_2| == |Seq|)
    ensures(multiset(Seq_1) + multiset(Seq_2) == multiset(Seq))
{
}

// ATOM 

proof fn Lemma_1(Seq_1: Seq, Seq_2: Seq)
    requires(multiset(Seq_1) == multiset(Seq_2))
    ensures(forall|x| x in Seq_1 ==> x in Seq_2)
{
}

// SPEC 

pub fn quickSort(Seq: Seq<int>) -> (Seq': Seq<int>)
    ensures(multiset(Seq) == multiset(Seq'))
{
}