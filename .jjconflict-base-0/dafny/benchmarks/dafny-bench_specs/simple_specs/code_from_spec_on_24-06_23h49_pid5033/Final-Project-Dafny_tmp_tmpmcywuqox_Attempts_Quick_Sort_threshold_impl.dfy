//IMPL threshold
method threshold(thres:int,Seq:seq<int>) returns (Seq_1:seq<int>,Seq_2:seq<int>)
 ensures (forall x | x in Seq_1 :: x <= thres) && (forall x | x in Seq_2 :: x >= thres)
 ensures |Seq_1| + |Seq_2| == |Seq| 
 ensures multiset(Seq_1) + multiset(Seq_2) == multiset(Seq)
{
    Seq_1 := [];
    Seq_2 := [];
    
    var i := 0;
    while i < |Seq|
        invariant 0 <= i <= |Seq|
        invariant forall x | x in Seq_1 :: x <= thres
        invariant forall x | x in Seq_2 :: x >= thres
        invariant multiset(Seq_1) + multiset(Seq_2) == multiset(Seq[..i])
        invariant |Seq_1| + |Seq_2| == i
    {
        /* code modified by LLM (iteration 4): fixed condition - elements <= thres go to Seq_1, elements > thres go to Seq_2 */
        if Seq[i] <= thres {
            Seq_1 := Seq_1 + [Seq[i]];
        } else {
            Seq_2 := Seq_2 + [Seq[i]];
        }
        i := i + 1;
    }
}