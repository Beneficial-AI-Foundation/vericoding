pub fn AnyValueExists(seq1: Seq<int>, seq2: Seq<int>) -> (result: bool)
    ensures(result <==> (exists|i: int| 0 <= i < seq1.len() && seq2.contains(seq1[i])))
{
}