// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method Multiply(a: int, b: int) returns (result: int)
  ensures result == a * b
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  if b == 0 {
    result := 0;
  } else if b > 0 {
    result := 0;
    var i := 0;
    while i < b
      invariant 0 <= i <= b
      invariant result == a * i
    {
      result := result + a;
      i := i + 1;
    }
  } else {
    result := 0;
    var i := 0;
    while i < -b
      invariant 0 <= i <= -b
      invariant result == a * i
    {
      result := result + a;
      i := i + 1;
    }
    result := -result;
  }
}
// </vc-code>
