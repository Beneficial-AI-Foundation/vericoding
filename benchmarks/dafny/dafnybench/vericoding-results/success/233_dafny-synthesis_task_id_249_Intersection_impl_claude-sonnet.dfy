predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

// <vc-helpers>
lemma InArrayExists(arr: array<int>, x: int, idx: int)
    requires 0 <= idx < arr.Length
    requires arr[idx] == x
    ensures InArray(arr, x)
{
}

predicate SeqContains(s: seq<int>, x: int)
{
    exists i :: 0 <= i < |s| && s[i] == x
}

lemma SeqContainsAppend(s: seq<int>, x: int)
    requires !SeqContains(s, x)
    ensures SeqContains(s + [x], x)
    ensures forall y :: y != x ==> (SeqContains(s + [x], y) <==> SeqContains(s, y))
{
    // Prove that x is in s + [x] at the last position
    assert (s + [x])[|s|] == x;
    assert |s + [x]| == |s| + 1;
    assert 0 <= |s| < |s + [x]|;
    
    // Prove SeqContains(s + [x], x)
    assert exists i :: 0 <= i < |s + [x]| && (s + [x])[i] == x;
    
    // Prove the equivalence for other elements
    forall y | y != x
        ensures SeqContains(s + [x], y) <==> SeqContains(s, y)
    {
        if SeqContains(s, y) {
            var i :| 0 <= i < |s| && s[i] == y;
            assert (s + [x])[i] == s[i] == y;
            assert 0 <= i < |s + [x]|;
        }
        
        if SeqContains(s + [x], y) {
            var i :| 0 <= i < |s + [x]| && (s + [x])[i] == y;
            if i < |s| {
                assert s[i] == (s + [x])[i] == y;
            } else {
                assert i == |s|;
                assert (s + [x])[i] == x;
                assert y == x;
                assert false;
            }
        }
    }
}

lemma SeqDistinctPreserved(s: seq<int>, x: int)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
    requires !SeqContains(s, x)
    ensures forall i, j :: 0 <= i < j < |s + [x]| ==> (s + [x])[i] != (s + [x])[j]
{
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
        invariant forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
    {
        var j := 0;
        var found := false;
        
        while j < b.Length && !found
            invariant 0 <= j <= b.Length
            invariant found ==> (j > 0 && b[j-1] == a[i])
            invariant !found ==> forall k :: 0 <= k < j ==> b[k] != a[i]
        {
            if b[j] == a[i] {
                found := true;
                InArrayExists(b, a[i], j);
            }
            j := j + 1;
        }
        
        if found && a[i] !in result {
            InArrayExists(a, a[i], i);
            SeqContainsAppend(result, a[i]);
            SeqDistinctPreserved(result, a[i]);
            result := result + [a[i]];
        }
        
        i := i + 1;
    }
}
// </vc-code>

