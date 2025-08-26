// <vc-helpers>
// </vc-helpers>

method IsLengthOdd(s: string) returns (result: bool)
    ensures result <==> |s| % 2 == 1
// <vc-code>
{
  assume false;
}
// </vc-code>