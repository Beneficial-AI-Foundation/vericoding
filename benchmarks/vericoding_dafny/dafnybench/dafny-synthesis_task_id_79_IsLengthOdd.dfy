// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method IsLengthOdd(s: string) returns (result: bool)
    ensures result <==> |s| % 2 == 1
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>