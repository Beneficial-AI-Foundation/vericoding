

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ArrayToSeq(a: array<int>) returns (s: seq<int>)
    requires a != null
    ensures |s| == a.Length
    ensures forall i :: 0 <= i < a.Length ==> s[i] == a[i]
// </vc-spec>
// <vc-code>
{
    var res := [];
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant |res| == i
        invariant forall j :: 0 <= j < i ==> res[j] == a[j]
    {
        res := res + [a[i]];
        i := i + 1;
    }
    s := res;
}
// </vc-code>

