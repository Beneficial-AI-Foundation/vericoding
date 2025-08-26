method IsLengthOdd(s: string) returns (result: bool)
    ensures result <==> |s| % 2 == 1
// </vc-spec>
// <vc-code>
{
  result := |s| % 2 == 1;
}
// </vc-code>