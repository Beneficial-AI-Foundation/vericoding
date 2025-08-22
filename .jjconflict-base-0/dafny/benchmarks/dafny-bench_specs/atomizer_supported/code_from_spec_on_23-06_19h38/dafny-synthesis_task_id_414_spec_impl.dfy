//IMPL 
method AnyValueExists(seq1: seq<int>, seq2: seq<int>) returns (result: bool)
    ensures result <==> (exists i :: 0 <= i < |seq1| && seq1[i] in seq2)
{
    result := false;
    var i := 0;
    while i < |seq1|
        invariant 0 <= i <= |seq1|
        invariant result <==> (exists j :: 0 <= j < i && seq1[j] in seq2)
    {
        if seq1[i] in seq2 {
            result := true;
            return;
        }
        i := i + 1;
    }
}