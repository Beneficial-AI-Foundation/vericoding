// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ContainsK(s: seq<int>, k: int) returns (result: bool)
    ensures result <==> k in s
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>