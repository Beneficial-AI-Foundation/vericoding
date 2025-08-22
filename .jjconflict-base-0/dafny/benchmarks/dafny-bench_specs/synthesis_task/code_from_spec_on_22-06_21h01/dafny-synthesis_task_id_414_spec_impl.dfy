//IMPL 
method AnyValueExists(seq1: seq<int>, seq2: seq<int>) returns (result: bool)
    ensures result <==> (exists i :: 0 <= i < |seq1| && seq1[i] in seq2)
{
    /* code modified by LLM (iteration 1): initialize result before loop */
    result := false;
    var i := 0;
    while i < |seq1|
        invariant 0 <= i <= |seq1|
        /* code modified by LLM (iteration 1): updated loop invariant to correctly express that no element found so far when result is false */
        invariant !result ==> (forall j :: 0 <= j < i ==> seq1[j] !in seq2)
        /* code modified by LLM (iteration 1): added invariant to handle case when result is true */
        invariant result ==> (exists j :: 0 <= j < i && seq1[j] in seq2)
    {
        if seq1[i] in seq2 {
            result := true;
            return;
        }
        i := i + 1;
    }
    result := false;
}