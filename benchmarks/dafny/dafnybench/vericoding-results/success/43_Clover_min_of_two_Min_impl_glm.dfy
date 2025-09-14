

// <vc-helpers>
// No helpers needed for this implementation.
// </vc-helpers>

// <vc-spec>
method Min(x: int, y:int) returns (z: int)
  ensures x<=y ==> z==x
  ensures x>y ==> z==y
// </vc-spec>
// <vc-code>
{
  z := if x <= y then x else y;
}
// </vc-code>

