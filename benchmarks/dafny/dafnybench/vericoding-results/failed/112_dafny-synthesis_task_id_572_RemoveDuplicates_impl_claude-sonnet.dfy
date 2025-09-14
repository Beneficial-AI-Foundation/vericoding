

// <vc-helpers>
lemma InSeqImpliesInArray(a: array<int>, s: seq<int>, x: int, bound: int)
    requires 0 <= bound <= a.Length
    requires forall y :: y in s <==> exists i :: 0 <= i < bound && a[i] == y
    requires x in s
    ensures exists i :: 0 <= i < bound && a[i] == x
{
}

lemma InArrayAndNotInSeqImpliesCanAdd(a: array<int>, s: seq<int>, x: int, bound: int, idx: int)
    requires 0 <= bound <= a.Length
    requires 0 <= idx < bound
    requires a[idx] == x
    requires x !in s
    requires forall y :: y in s ==> exists i :: 0 <= i < bound && a[i] == y
    ensures forall y :: y in s + [x] ==> exists i :: 0 <= i < bound && a[i] == y
{
}

lemma NoDuplicatesPreserved(s: seq<int>, x: int)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
    requires x !in s
    ensures forall i, j :: 0 <= i < j < |s + [x]| ==> (s + [x])[i] != (s + [x])[j]
{
}
// </vc-helpers>

// <vc-spec>
method RemoveDuplicates(a: array<int>) returns (result: seq<int>)
    requires a != null
    ensures forall x :: x in result <==> exists i :: 0 <= i < a.Length && a[i] == x
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
{
    result := [];
    var i := 0;
    
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall x :: x in result <==> exists j :: 0 <= j < i && a[j] == x
        invariant forall k, l :: 0 <= k < l < |result| ==> result[k] != result[l]
    {
        if a[i] !in result {
            InArrayAndNotInSeqImpliesCanAdd(a, result, a[i], i + 1, i);
            NoDuplicatesPreserved(result, a[i]);
            result := result + [a[i]];
        }
        i := i + 1;
    }
}
// </vc-code>

