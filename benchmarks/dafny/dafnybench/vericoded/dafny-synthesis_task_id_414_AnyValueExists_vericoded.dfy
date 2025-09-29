

// <vc-helpers>
lemma AnyValueExistsHelper(seq1: seq<int>, seq2: seq<int>, k: int)
    requires 0 <= k <= |seq1|
    ensures (exists i :: 0 <= i < k && seq1[i] in seq2) == (exists i :: 0 <= i < |seq1| && i < k && seq1[i] in seq2)
{
    // This lemma is trivially true by the definition of bounded quantification
}
// </vc-helpers>

// <vc-spec>
method AnyValueExists(seq1: seq<int>, seq2: seq<int>) returns (result: bool)
    ensures result <==> (exists i :: 0 <= i < |seq1| && seq1[i] in seq2)
// </vc-spec>
// <vc-code>
{
    result := false;
    var index := 0;
    
    while index < |seq1|
        invariant 0 <= index <= |seq1|
        invariant result <==> (exists i :: 0 <= i < index && seq1[i] in seq2)
    {
        if seq1[index] in seq2 {
            result := true;
            assert seq1[index] in seq2;
            assert 0 <= index < index + 1 <= |seq1|;
            assert exists i :: 0 <= i < index + 1 && seq1[i] in seq2;
        }
        index := index + 1;
    }
    
    assert index == |seq1|;
    assert result <==> (exists i :: 0 <= i < |seq1| && seq1[i] in seq2);
}
// </vc-code>

