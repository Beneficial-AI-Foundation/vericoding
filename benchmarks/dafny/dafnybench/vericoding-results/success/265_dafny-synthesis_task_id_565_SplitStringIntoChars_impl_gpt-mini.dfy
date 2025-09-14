

// <vc-helpers>
// Helper section intentionally left empty.
// </vc-helpers>

// <vc-spec>
method SplitStringIntoChars(s: string) returns (v: seq<char>)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> v[i] == s[i]
// </vc-spec>
// <vc-code>
{
  v := s;
}
// </vc-code>

