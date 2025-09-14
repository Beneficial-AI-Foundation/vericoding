predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

// <vc-helpers>
lemma InSeqImpliesExists(s: seq<int>, x: int)
    requires x in s
    ensures exists i :: 0 <= i < |s| && s[i] == x
{
}

lemma NotInSeqImpliesForall(s: seq<int>, x: int)
    requires x !in s
    ensures forall i :: 0 <= i < |s| ==> s[i] != x
{
}

lemma SeqNoDupsPreserved(s: seq<int>, x: int)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
    requires x !in s
    ensures forall i, j :: 0 <= i < j < |s + [x]| ==> (s + [x])[i] != (s + [x])[j]
{
    var newSeq := s + [x];
    forall i, j | 0 <= i < j < |newSeq|
        ensures newSeq[i] != newSeq[j]
    {
        if j == |s| {
            assert newSeq[j] == x;
            assert newSeq[i] == s[i];
            assert x !in s;
            NotInSeqImpliesForall(s, x);
            assert s[i] != x;
        } else {
            assert newSeq[i] == s[i] && newSeq[j] == s[j];
        }
    }
}
// </vc-helpers>

// <vc-spec>
method DissimilarElements(a: array<int>, b: array<int>) returns (result: seq<int>)
    // All elements in the output are either in a or b, but not in both or neither
    ensures forall x :: x in result ==> (InArray(a, x) != InArray(b, x))
    // The elements in the output are all different
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
{
    result := [];
    
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall x :: x in result ==> (InArray(a, x) != InArray(b, x))
        invariant forall k, l :: 0 <= k < l < |result| ==> result[k] != result[l]
    {
        var inB := false;
        var j := 0;
        while j < b.Length
            invariant 0 <= j <= b.Length
            invariant inB <==> exists k :: 0 <= k < j && b[k] == a[i]
        {
            if b[j] == a[i] {
                inB := true;
            }
            j := j + 1;
        }
        
        if !inB && a[i] !in result {
            SeqNoDupsPreserved(result, a[i]);
            result := result + [a[i]];
        }
        i := i + 1;
    }
    
    i := 0;
    while i < b.Length
        invariant 0 <= i <= b.Length
        invariant forall x :: x in result ==> (InArray(a, x) != InArray(b, x))
        invariant forall k, l :: 0 <= k < l < |result| ==> result[k] != result[l]
    {
        var inA := false;
        var j := 0;
        while j < a.Length
            invariant 0 <= j <= a.Length
            invariant inA <==> exists k :: 0 <= k < j && a[k] == b[i]
        {
            if a[j] == b[i] {
                inA := true;
            }
            j := j + 1;
        }
        
        if !inA && b[i] !in result {
            SeqNoDupsPreserved(result, b[i]);
            result := result + [b[i]];
        }
        i := i + 1;
    }
}
// </vc-code>

