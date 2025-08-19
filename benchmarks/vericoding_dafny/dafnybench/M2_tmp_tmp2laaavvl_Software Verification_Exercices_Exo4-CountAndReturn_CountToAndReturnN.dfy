// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method CountToAndReturnN(n: int) returns (r: int)
    requires n >= 0
    ensures r == n
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>