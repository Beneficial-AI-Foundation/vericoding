

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SmallestListLength(s: seq<seq<int>>) returns (v: int)
    requires |s| > 0
    ensures forall i :: 0 <= i < |s| ==> v <= |s[i]|
    ensures exists i :: 0 <= i < |s| && v == |s[i]|
// </vc-spec>
// <vc-code>
{
    v := |s[0]|;
    var idx := 1;
    
    while idx < |s|
        invariant 1 <= idx <= |s|
        invariant forall i :: 0 <= i < idx ==> v <= |s[i]|
        invariant exists i :: 0 <= i < idx && v == |s[i]|
    {
        if |s[idx]| < v {
            v := |s[idx]|;
        }
        idx := idx + 1;
    }
}
// </vc-code>

