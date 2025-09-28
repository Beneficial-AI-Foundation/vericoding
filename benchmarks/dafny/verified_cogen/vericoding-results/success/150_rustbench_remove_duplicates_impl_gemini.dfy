// <vc-preamble>
predicate InArray(a: seq<int>, x: int)
{
    exists i :: 0 <= i < |a| && a[i] == x
}
// </vc-preamble>

// <vc-helpers>
predicate IsDistinct(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}
// </vc-helpers>

// <vc-spec>
method RemoveDuplicates(a: array<int>) returns (result: array<int>)
    requires a.Length >= 1
    ensures forall i :: 0 <= i < result.Length ==> InArray(a[..], result[i])
    ensures forall i, j :: 0 <= i < j < result.Length ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
{
    var uniques: seq<int> := [];
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant IsDistinct(uniques)
        invariant forall k :: 0 <= k < |uniques| ==> InArray(a[..i], uniques[k])
    {
        var x := a[i];
        if x !in uniques {
            uniques := uniques + [x];
        }
        i := i + 1;
    }

    result := new int[|uniques|];
    var j := 0;
    while j < |uniques|
        invariant 0 <= j <= |uniques|
        invariant result.Length == |uniques|
        invariant result[..j] == uniques[..j]
    {
        result[j] := uniques[j];
        j := j + 1;
    }
}
// </vc-code>
