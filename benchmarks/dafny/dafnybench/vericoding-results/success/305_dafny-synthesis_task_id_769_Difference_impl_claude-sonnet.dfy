

// <vc-helpers>
predicate IsDistinct(s: seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

lemma DistinctPreservation(s: seq<int>, x: int)
    requires IsDistinct(s)
    requires x !in s
    ensures IsDistinct(s + [x])
{
    var result := s + [x];
    forall i, j | 0 <= i < j < |result|
        ensures result[i] != result[j]
    {
        if j == |s| {
            assert result[j] == x;
            assert result[i] == s[i];
            assert x !in s;
            assert result[i] != result[j];
        } else {
            assert result[i] == s[i];
            assert result[j] == s[j];
            assert s[i] != s[j];
        }
    }
}
// </vc-helpers>

// <vc-spec>
method Difference(a: seq<int>, b: seq<int>) returns (diff: seq<int>)
    ensures forall x :: x in diff <==> (x in a && x !in b)
    ensures forall i, j :: 0 <= i < j < |diff| ==> diff[i] != diff[j]
// </vc-spec>
// <vc-code>
{
    diff := [];
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant forall x :: x in diff <==> (x in a[..i] && x !in b)
        invariant IsDistinct(diff)
    {
        if a[i] in b {
            i := i + 1;
        } else if a[i] in diff {
            i := i + 1;
        } else {
            DistinctPreservation(diff, a[i]);
            diff := diff + [a[i]];
            i := i + 1;
        }
    }
}
// </vc-code>

