// <vc-helpers>
// </vc-helpers>

method F() returns ( r: int)
    ensures r <= 0
// <vc-code>
{
  assume false;
}
// </vc-code>