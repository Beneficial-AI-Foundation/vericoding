// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Abs(x: int): int { if x >= 0 then x else -x }
// </vc-helpers>

// <vc-spec>
method multiply(a: int, b: int) returns (result: int)
    ensures result == a * b
// </vc-spec>
// <vc-code>
{
  var s := if b >= 0 then 1 else -1;
  var m := Abs(b);
  var i := 0;
  result := 0;
  while i < m
    invariant 0 <= i <= m
    invariant result == a * i
    decreases m - i
  {
    result := result + a;
    i := i + 1;
  }
  if s == -1 {
    result := -result;
  }
}
// </vc-code>
