// ATOM 
predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

//IMPL 
method RemoveElements(a: array<int>, b: array<int>) returns (result: seq<int>)
    // All elements in the output are in a and not in b
    ensures forall x :: x in result ==> InArray(a, x) && !InArray(b, x)
    // The elements in the output are all different
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{
    result := [];
    
    for i := 0 to a.Length
        invariant forall x :: x in result ==> InArray(a, x) && !InArray(b, x)
        invariant forall k, j :: 0 <= k < j < |result| ==> result[k] != result[j]
    {
        if !InArray(b, a[i]) && a[i] !in result {
            result := result + [a[i]];
        }
    }
}