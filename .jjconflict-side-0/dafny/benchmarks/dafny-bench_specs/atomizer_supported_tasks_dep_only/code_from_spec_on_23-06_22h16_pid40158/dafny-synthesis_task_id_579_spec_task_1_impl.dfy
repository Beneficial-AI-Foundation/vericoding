// ATOM 
predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

//IMPL 
method DissimilarElements(a: array<int>, b: array<int>) returns (result: seq<int>)
    // All elements in the output are either in a or b, but not in both or neither
    ensures forall x :: x in result ==> (InArray(a, x) != InArray(b, x))
    // The elements in the output are all different
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{
    result := [];
    var i := 0;
    
    // Process elements from array a
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall x :: x in result ==> (InArray(a, x) != InArray(b, x))
        invariant forall k, l :: 0 <= k < l < |result| ==> result[k] != result[l]
    {
        if !InArray(b, a[i]) && a[i] !in result {
            result := result + [a[i]];
        }
        i := i + 1;
    }
    
    i := 0;
    // Process elements from array b
    while i < b.Length
        invariant 0 <= i <= b.Length
        invariant forall x :: x in result ==> (InArray(a, x) != InArray(b, x))
        invariant forall k, l :: 0 <= k < l < |result| ==> result[k] != result[l]
    {
        if !InArray(a, b[i]) && b[i] !in result {
            result := result + [b[i]];
        }
        i := i + 1;
    }
}