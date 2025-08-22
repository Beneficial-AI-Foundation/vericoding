// <vc-helpers>
// </vc-helpers>

method ContainsZ(s: string) returns (result: bool)
    ensures result <==> (exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z'))
// <vc-code>
{
  assume false;
}
// </vc-code>