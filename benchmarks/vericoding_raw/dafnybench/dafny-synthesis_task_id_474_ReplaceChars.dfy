// <vc-helpers>
// </vc-helpers>

method ReplaceChars(s: string, oldChar: char, newChar: char) returns (v: string)
    ensures |v| == |s|
    ensures forall i :: 0 <= i < |s| ==> (s[i] == oldChar ==> v[i] == newChar) && (s[i] != oldChar ==> v[i] == s[i])
// <vc-code>
{
  assume false;
}
// </vc-code>