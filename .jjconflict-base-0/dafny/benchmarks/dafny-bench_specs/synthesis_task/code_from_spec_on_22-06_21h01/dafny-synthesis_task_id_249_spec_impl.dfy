// ATOM
predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

// IMPL
method Intersection(a: array<int>, b: array<int>) returns (result: seq<int>)
    // All elements in the output are in both a and b
    ensures forall x :: x in result ==> (InArray(a, x) && InArray(b, x))
    // The elements in the output are all different
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{
    result := [];
    var i := 0;
    
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall x :: x in result ==> (InArray(a, x) && InArray(b, x))
        invariant forall k, l :: 0 <= k < l < |result| ==> result[k] != result[l]
    {
        if InArray(b, a[i]) && a[i] !in result {
            result := result + [a[i]];
        }
        i := i + 1;
    }
}