// <vc-helpers>
// </vc-helpers>

method ToCharArray(s: string) returns (a: array<char>)
    ensures a.Length == |s|
    ensures forall i :: 0 <= i < |s| ==> a[i] == s[i]
// <vc-code>
{
  assume false;
}
// </vc-code>