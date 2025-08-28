// <vc-helpers>
// No additional helpers or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method ArrayToSeq(a: array<int>) returns (s: seq<int>)
    requires a != null
    ensures |s| == a.Length
    ensures forall i :: 0 <= i < a.Length ==> s[i] == a[i]
// </vc-spec>
// </vc-spec>

// <vc-code>
method ArrayToSeqImpl(a: array<int>) returns (s: seq<int>)
    ensures |s| == a.Length
    ensures forall i :: 0 <= i < a.Length ==> s[i] == a[i]
{
    s := [];
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant |s| == i
        invariant forall k :: 0 <= k < i ==> s[k] == a[k]
    {
        s := s + [a[i]];
        i := i + 1;
    }
}
// </vc-code>
