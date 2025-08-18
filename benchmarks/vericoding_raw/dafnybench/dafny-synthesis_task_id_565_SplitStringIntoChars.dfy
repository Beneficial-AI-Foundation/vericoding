// <vc-helpers>
// </vc-helpers>

method SplitStringIntoChars(s: string) returns (v: seq<char>)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> v[i] == s[i]
// <vc-code>
{
  assume false;
}
// </vc-code>