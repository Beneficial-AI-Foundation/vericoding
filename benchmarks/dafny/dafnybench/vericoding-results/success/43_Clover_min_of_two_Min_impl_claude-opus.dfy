

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Min(x: int, y:int) returns (z: int)
  ensures x<=y ==> z==x
  ensures x>y ==> z==y
// </vc-spec>
// <vc-code>
{
  if x <= y {
    z := x;
  } else {
    z := y;
  }
}
// </vc-code>

