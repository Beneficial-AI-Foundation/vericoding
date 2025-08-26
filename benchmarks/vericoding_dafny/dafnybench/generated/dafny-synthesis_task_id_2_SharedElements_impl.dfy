predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

// <vc-helpers>
predicate InSeq(s: seq<int>, x: int)
{
    exists i :: 0 <= i < |s| && s[i] == x
}
// </vc-helpers>

// <vc-spec>
method SharedElements(a: array<int>, b: array<int>) returns (result: seq<int>)
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
        invariant forall k, l :: 0 <= k < l < |result| ==> result[k] != result[l]
    {
        var current := a[i];
        
        // Check if current is in array b
        var j := 0;
        var foundInB := false;
        
        while j < b.Length && !foundInB
            invariant 0 <= j <= b.Length
            invariant foundInB ==> InArray(b, current)
            invariant !foundInB ==> forall k :: 0 <= k < j ==> b[k] != current
        {
            if b[j] == current {
                foundInB := true;
            }
            j := j + 1;
        }
        
        // If found in b and not already in result, add it
        if foundInB && !InSeq(result, current) {
            result := result + [current];
        }
        
        i := i + 1;
    }
}
// </vc-code>