predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

// <vc-helpers>
predicate NotInArray(a: array<int>, x: int)
    reads a
{
    !InArray(a, x)
}

predicate InSeq(s: seq<int>, x: int)
{
    x in s
}

lemma InArrayImpliesExists(a: array<int>, x: int)
    requires InArray(a, x)
    ensures exists i :: 0 <= i < a.Length && a[i] == x
{
    // This follows directly from the definition of InArray
}

lemma NotInArrayImpliesForAll(a: array<int>, x: int)
    requires NotInArray(a, x)
    ensures forall i :: 0 <= i < a.Length ==> a[i] != x
{
    // This follows from the negation of InArray
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
    
    // Add elements from a that are not in b
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall x :: x in result ==> (InArray(a, x) != InArray(b, x))
        invariant forall j, k :: 0 <= j < k < |result| ==> result[j] != result[k]
        invariant forall x :: x in result ==> InArray(a, x) && NotInArray(b, x)
    {
        if NotInArray(b, a[i]) && a[i] !in result {
            result := result + [a[i]];
        }
        i := i + 1;
    }
    
    // Add elements from b that are not in a
    var j := 0;
    while j < b.Length
        invariant 0 <= j <= b.Length
        invariant forall x :: x in result ==> (InArray(a, x) != InArray(b, x))
        invariant forall k, l :: 0 <= k < l < |result| ==> result[k] != result[l]
    {
        if NotInArray(a, b[j]) && b[j] !in result {
            result := result + [b[j]];
        }
        j := j + 1;
    }
}
// </vc-code>

