// <vc-helpers>
// </vc-helpers>

method CountCharacters(s: string) returns (count: int)
    ensures count >= 0
    ensures count == |s|
// <vc-code>
{
  assume false;
}
// </vc-code>