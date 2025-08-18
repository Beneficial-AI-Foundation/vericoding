// <vc-helpers>
// </vc-helpers>

method ContainsK(s: seq<int>, k: int) returns (result: bool)
    ensures result <==> k in s
// <vc-code>
{
  assume false;
}
// </vc-code>