// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method GcdInt(a: int, b: int) returns (result: int)
    ensures
        result > 0 &&
        a % result == 0 &&
        b % result == 0 &&
        (forall d :: d > 0 && a % d == 0 && b % d == 0 ==> d <= result)
// </vc-spec>
// <vc-code>
{
  var a_abs := if a < 0 then -a else a;
  var b_abs := if b < 0 then -b else b;
  var x := a_abs;
  var y := b_abs;
  while y != 0
  {
    var t := y;
    y := x % y;
    x := t;
  }
  result := x;
}
// </vc-code>
