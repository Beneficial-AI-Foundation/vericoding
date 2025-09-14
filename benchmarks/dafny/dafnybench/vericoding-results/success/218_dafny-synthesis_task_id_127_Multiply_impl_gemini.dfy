// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Multiply(a: int, b: int) returns (result: int)
  ensures result == a * b
// </vc-spec>
// <vc-code>
{
  if b >= 0 {
    result := 0;
    var i := 0;
    while i < b
      invariant 0 <= i <= b
      invariant result == a * i
    {
      result := result + a;
      i := i + 1;
    }
  } else { // b < 0
    result := 0;
    var i := b;
    while i < 0
      invariant b <= i <= 0
      invariant result == a * (b - i)
    {
      result := result - a;
      i := i + 1;
    }
  }
}
// </vc-code>
