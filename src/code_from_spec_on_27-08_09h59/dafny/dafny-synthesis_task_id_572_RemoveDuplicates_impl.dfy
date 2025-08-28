// <vc-helpers>
predicate Contains(s: seq<int>, x: int)
{
    exists i :: 0 <= i < |s| && s[i] == x
}

lemma ContainsEquivalence(s: seq<int>, x: int)
    ensures Contains(s, x) <==> x in s
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method RemoveDuplicates(a: array<int>) returns (result: seq<int>)
    requires a != null
    ensures forall x :: x in result <==> exists i :: 0 <= i < a.Length && a[i] == x
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
// </vc-spec>
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
            result := result + [a[i]];
        }
        i := i + 1;
    }
}
// </vc-code>
