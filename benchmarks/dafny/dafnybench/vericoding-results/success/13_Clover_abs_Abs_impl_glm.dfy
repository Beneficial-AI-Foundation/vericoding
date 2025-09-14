

// <vc-helpers>
// No helper code needed for this specification.
// </vc-helpers>

// <vc-spec>
method Abs(x: int) returns (y: int)
  ensures x>=0 ==> x==y
  ensures x<0 ==> x+y==0
// </vc-spec>
// <vc-code>
{
  if x >= 0 {
    return x;
  } else {
    return -x;
  }
}
// </vc-code>

