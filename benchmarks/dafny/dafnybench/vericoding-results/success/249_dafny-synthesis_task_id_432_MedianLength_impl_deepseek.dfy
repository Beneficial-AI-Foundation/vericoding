

// <vc-helpers>
lemma DivisionProperty(x: int, y: int)
  requires x > 0
  requires y > 0
  ensures (x + y) / 2 > 0
{
}

lemma MedianTheorem(a: int, b: int)
  requires a > 0 && b > 0
  ensures (a + b) / 2 == (if a < b then (b - a) / 2 + a else (a - b) / 2 + b)
{
}
// </vc-helpers>

// <vc-spec>
method MedianLength(a: int, b: int) returns (median: int)
    requires a > 0 && b > 0
    ensures median == (a + b) / 2
// </vc-spec>
// <vc-code>
{
  if a < b {
    median := (b - a) / 2 + a;
  } else {
    median := (a - b) / 2 + b;
  }
}
// </vc-code>

