

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
    var s_arr := new int[a.Length];
    for i := 0 to a.Length - 1
        invariant 0 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> s_arr[k] == a[k]
    {
        s_arr[i] := a[i];
    }
    return s_arr[..a.Length];
}
// </vc-code>

