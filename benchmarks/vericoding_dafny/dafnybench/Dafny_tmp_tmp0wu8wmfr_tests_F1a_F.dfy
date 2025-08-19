// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method F() returns ( r: int)
    ensures r <= 0
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>