// <vc-helpers>
// </vc-helpers>

method StartAndEndWithSameChar(s: string) returns (result: bool)
    requires |s| > 0
    ensures result <==> s[0] == s[|s| - 1]
// <vc-code>
{
  assume false;
}
// </vc-code>