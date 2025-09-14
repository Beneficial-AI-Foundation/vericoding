

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method AppendArrayToSeq(s: seq<int>, a: array<int>) returns (r: seq<int>)
    requires a != null
    ensures |r| == |s| + a.Length
    ensures forall i :: 0 <= i < |s| ==> r[i] == s[i]
    ensures forall i :: 0 <= i < a.Length ==> r[|s| + i] == a[i]
// </vc-spec>
// <vc-code>
{
    var r_array: array<int> := new int[|s| + a.Length];

    for i := 0 to |s|-1
        invariant 0 <= i <= |s|
        invariant forall j :: 0 <= j < i ==> r_array[j] == s[j]
    {
        r_array[i] := s[i];
    }

    for i := 0 to a.Length-1
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> r_array[|s| + j] == a[j]
        invariant forall j :: 0 <= j < |s| ==> r_array[j] == s[j]
    {
        r_array[|s| + i] := a[i];
    }

    return r_array[..];
}
// </vc-code>

