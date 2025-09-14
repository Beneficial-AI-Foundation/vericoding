predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

// <vc-helpers>
lemma InArrayMembership(a: array<int>, x: int)
    ensures InArray(a, x) <==> exists i :: 0 <= i < a.Length && a[i] == x
{
}

lemma NotInArrayMembership(a: array<int>, x: int)
    ensures !InArray(a, x) <==> forall i :: 0 <= i < a.Length ==> a[i] != x
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
        var shouldAdd := true;
        
        // Check if a[i] is in b
        var j := 0;
        while j < b.Length && shouldAdd
            invariant 0 <= j <= b.Length
            invariant shouldAdd ==> forall k :: 0 <= k < j ==> b[k] != a[i]
        {
            if b[j] == a[i] {
                shouldAdd := false;
            }
            j := j + 1;
        }
        
        // Check if a[i] is already in result
        if shouldAdd {
            var k := 0;
            while k < |result| && shouldAdd
                invariant 0 <= k <= |result|
                invariant shouldAdd ==> forall m :: 0 <= m < k ==> result[m] != a[i]
            {
                if result[k] == a[i] {
                    shouldAdd := false;
                }
                k := k + 1;
            }
        }
        
        if shouldAdd {
            result := result + [a[i]];
        }
        
        i := i + 1;
    }
}
// </vc-code>

