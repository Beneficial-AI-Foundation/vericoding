// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function abs(n: int): int
  ensures 0 <= abs(n)
{
  if n < 0 then -n else n
}
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
  var x := abs(a);
  var y := abs(b);
  if x == 0 {
    if y == 0 {
      result := 1;
    } else {
      result := y;
    }
  } else if y == 0 {
    result := x;
  } else {
    var temp;
    while y != 0 {
      temp := x % y;
      x := y;
      y := temp;
    }
    result := x;
  }
}
// </vc-code>
