

// <vc-helpers>
lemma InSeqExists(s: seq<int>, x: int)
    requires x in s
    ensures exists i :: 0 <= i < |s| && s[i] == x
{
}

lemma NotInSeqForall(s: seq<int>, x: int)
    requires forall i :: 0 <= i < |s| ==> s[i] != x
    ensures x !in s
{
}
// </vc-helpers>

// <vc-spec>
method SmallestMissingNumber(s: seq<int>) returns (v: int)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
    ensures 0 <= v
    ensures v !in s
    ensures forall k :: 0 <= k < v ==> k in s
// </vc-spec>
// <vc-code>
{
    v := 0;
    var i := 0;
    
    while i < |s|
        invariant 0 <= i <= |s|
        invariant 0 <= v <= i
        invariant forall k :: 0 <= k < v ==> k in s
        invariant v !in s[..i]
        invariant i < |s| ==> v <= s[i] || s[i] < v
    {
        if s[i] == v {
            v := v + 1;
        }
        i := i + 1;
    }
    
    assert v !in s[..|s|];
    assert s[..|s|] == s;
}
// </vc-code>

