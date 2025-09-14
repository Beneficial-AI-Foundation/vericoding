// <vc-preamble>
predicate NthUglyNumberPrecond(n: nat)
{
    n > 0
}
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
function min3(a: int, b: int, c: int): int { min(min(a, b), c) }
// </vc-helpers>

// <vc-spec>
method NthUglyNumber(n: int) returns (result: int)
    requires n > 0
    ensures result > 0
// </vc-spec>
// <vc-code>
{
  var uglies := new int[n];
  uglies[0] := 1;
  var i := 1;
  var i2 := 0;
  var i3 := 0;
  var i5 := 0;
  while i < n
    invariant n > 0
    invariant 1 <= i <= n
    invariant 0 <= i2 < i && 0 <= i3 < i && 0 <= i5 < i
    invariant uglies[0] == 1
    invariant forall k :: 0 <= k < i ==> uglies[k] > 0
    decreases n - i
  {
    var next2 := 2 * uglies[i2];
    var next3 := 3 * uglies[i3];
    var next5 := 5 * uglies[i5];
    var next := min3(next2, next3, next5);
    uglies[i] := next;
    i := i + 1;
    if next == next2 {
      i2 := i2 + 1;
    }
    if next == next3 {
      i3 := i3 + 1;
    }
    if next == next5 {
      i5 := i5 + 1;
    }
  }
  result := uglies[n - 1];
}
// </vc-code>
