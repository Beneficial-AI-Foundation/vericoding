predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

// <vc-helpers>
lemma InArrayElement(a: array<int>, i: int)
    requires 0 <= i < a.Length
    ensures InArray(a, a[i])
{
    assert a[i] == a[i];
}

predicate InSeq(s: seq<int>, x: int)
{
    exists i :: 0 <= i < |s| && s[i] == x
}

lemma NotInSeqImpliesAllDifferent(s: seq<int>, x: int)
    requires forall i :: 0 <= i < |s| ==> s[i] != x
    ensures !InSeq(s, x)
{
}

lemma SeqUniqueAppend(s: seq<int>, x: int)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
    requires !InSeq(s, x)
    ensures forall i, j :: 0 <= i < j < |s + [x]| ==> (s + [x])[i] != (s + [x])[j]
{
    assert forall i :: 0 <= i < |s| ==> (s + [x])[i] == s[i];
    assert (s + [x])[|s|] == x;
    
    forall i, j | 0 <= i < j < |s + [x]|
        ensures (s + [x])[i] != (s + [x])[j]
    {
        if j < |s| {
            assert (s + [x])[i] == s[i];
            assert (s + [x])[j] == s[j];
            assert s[i] != s[j];
        } else {
            assert j == |s|;
            assert (s + [x])[j] == x;
            if i < |s| {
                assert (s + [x])[i] == s[i];
                assert s[i] != x;
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method Intersection(a: array<int>, b: array<int>) returns (result: seq<int>)
    // All elements in the output are in both a and b
    ensures forall x :: x in result ==> (InArray(a, x) && InArray(b, x))
    // The elements in the output are all different
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
{
    result := [];
    
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall x :: x in result ==> (InArray(a, x) && InArray(b, x))
        invariant forall k, j :: 0 <= k < j < |result| ==> result[k] != result[j]
    {
        var elem := a[i];
        
        // Check if elem is in array b
        var inB := false;
        var j := 0;
        while j < b.Length
            invariant 0 <= j <= b.Length
            invariant inB ==> InArray(b, elem)
            invariant !inB ==> forall k :: 0 <= k < j ==> b[k] != elem
        {
            if b[j] == elem {
                inB := true;
                InArrayElement(b, j);
                break;
            }
            j := j + 1;
        }
        
        if inB {
            // Check if elem is already in result
            var alreadyInResult := false;
            var k := 0;
            while k < |result|
                invariant 0 <= k <= |result|
                invariant alreadyInResult ==> InSeq(result, elem)
                invariant !alreadyInResult ==> forall m :: 0 <= m < k ==> result[m] != elem
            {
                if result[k] == elem {
                    alreadyInResult := true;
                    break;
                }
                k := k + 1;
            }
            
            if !alreadyInResult {
                NotInSeqImpliesAllDifferent(result, elem);
                SeqUniqueAppend(result, elem);
                InArrayElement(a, i);
                result := result + [elem];
            }
        }
        
        i := i + 1;
    }
}
// </vc-code>

