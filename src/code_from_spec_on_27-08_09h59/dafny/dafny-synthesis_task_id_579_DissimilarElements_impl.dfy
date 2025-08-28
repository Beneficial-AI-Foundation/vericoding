predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

// <vc-helpers>
lemma InSeqImpliesInArray(s: seq<int>, a: array<int>)
    requires forall x :: x in s ==> InArray(a, x)
    ensures forall i :: 0 <= i < |s| ==> InArray(a, s[i])
{
}

lemma NotInSeqImpliesNotInArray(s: seq<int>, a: array<int>)
    requires forall x :: x in s ==> !InArray(a, x)
    ensures forall i :: 0 <= i < |s| ==> !InArray(a, s[i])
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method DissimilarElements(a: array<int>, b: array<int>) returns (result: seq<int>)
    // All elements in the output are either in a or b, but not in both or neither
    ensures forall x :: x in result ==> (InArray(a, x) != InArray(b, x))
    // The elements in the output are all different
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    result := [];
    var i := 0;
    
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall x :: x in result ==> (InArray(a, x) != InArray(b, x))
        invariant forall k, j :: 0 <= k < j < |result| ==> result[k] != result[j]
    {
        var inB := false;
        var j := 0;
        
        while j < b.Length
            invariant 0 <= j <= b.Length
            invariant inB ==> exists k :: 0 <= k < j && b[k] == a[i]
            invariant !inB ==> forall k :: 0 <= k < j ==> b[k] != a[i]
        {
            if b[j] == a[i] {
                inB := true;
            }
            j := j + 1;
        }
        
        if !inB && a[i] !in result {
            result := result + [a[i]];
        }
        
        i := i + 1;
    }
    
    i := 0;
    while i < b.Length
        invariant 0 <= i <= b.Length
        invariant forall x :: x in result ==> (InArray(a, x) != InArray(b, x))
        invariant forall k, j :: 0 <= k < j < |result| ==> result[k] != result[j]
    {
        var inA := false;
        var j := 0;
        
        while j < a.Length
            invariant 0 <= j <= a.Length
            invariant inA ==> exists k :: 0 <= k < j && a[k] == b[i]
            invariant !inA ==> forall k :: 0 <= k < j ==> a[k] != b[i]
        {
            if a[j] == b[i] {
                inA := true;
            }
            j := j + 1;
        }
        
        if !inA && b[i] !in result {
            result := result + [b[i]];
        }
        
        i := i + 1;
    }
}
// </vc-code>
