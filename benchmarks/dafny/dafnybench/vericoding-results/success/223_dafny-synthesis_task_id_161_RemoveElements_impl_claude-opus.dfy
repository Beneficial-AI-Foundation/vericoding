predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

// <vc-helpers>
lemma InArrayNegation(a: array<int>, x: int)
    ensures !InArray(a, x) <==> forall i :: 0 <= i < a.Length ==> a[i] != x
{
}

lemma NotInSequence(s: seq<int>, x: int)
    ensures (x !in s) <==> (forall i :: 0 <= i < |s| ==> s[i] != x)
{
}
// </vc-helpers>

// <vc-spec>
method RemoveElements(a: array<int>, b: array<int>) returns (result: seq<int>)
    // All elements in the output are in a and not in b
    ensures forall x :: x in result ==> InArray(a, x) && !InArray(b, x)
    // The elements in the output are all different
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
{
    result := [];
    var i := 0;
    
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall x :: x in result ==> InArray(a, x) && !InArray(b, x)
        invariant forall j, k :: 0 <= j < k < |result| ==> result[j] != result[k]
    {
        var elem := a[i];
        
        // Check if elem is in b
        var inB := false;
        var j := 0;
        while j < b.Length
            invariant 0 <= j <= b.Length
            invariant inB <==> exists k :: 0 <= k < j && b[k] == elem
        {
            if b[j] == elem {
                inB := true;
            }
            j := j + 1;
        }
        
        // Check if elem is already in result
        var inResult := false;
        var k := 0;
        while k < |result|
            invariant 0 <= k <= |result|
            invariant inResult <==> exists m :: 0 <= m < k && result[m] == elem
        {
            if result[k] == elem {
                inResult := true;
            }
            k := k + 1;
        }
        
        // Add to result if not in b and not already in result
        if !inB && !inResult {
            assert !InArray(b, elem);
            assert InArray(a, elem);
            result := result + [elem];
        }
        
        i := i + 1;
    }
}
// </vc-code>

