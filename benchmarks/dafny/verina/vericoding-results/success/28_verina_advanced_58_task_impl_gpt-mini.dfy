// <vc-preamble>
predicate NthUglyNumberPrecond(n: nat)
{
    n > 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Min3 utility to compute minimum of three integers */
function Min3(a: int, b: int, c: int): int { if a <= b && a <= c then a else if b <= c then b else c }
// </vc-helpers>

// <vc-spec>
method NthUglyNumber(n: int) returns (result: int)
    requires n > 0
    ensures result > 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implement ugly number generator with proper invariants */
  var uglies := new int[n];
  uglies[0] := 1;
  var i2 := 0;
  var i3 := 0;
  var i5 := 0;
  var k := 1;
  while k < n
    invariant 1 <= n
    invariant 1 <= k <= n
    invariant 0 <= i2 <= k - 1
    invariant 0 <= i3 <= k - 1
    invariant 0 <= i5 <= k - 1
    invariant forall j :: 0 <= j < k ==> uglies[j] > 0
  {
    var val2 := uglies[i2] * 2;
    var val3 := uglies[i3] * 3;
    var val5 := uglies[i5] * 5;
    var next := Min3(val2, val3, val5);
    uglies[k] := next;
    if next == val2 { i2 := i2 + 1; }
    if next == val3 { i3 := i3 + 1; }
    if next == val5 { i5 := i5 + 1; }
    k := k + 1;
  }
  result := uglies[n - 1];
}
// </vc-code>
