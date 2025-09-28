// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function Abs(x: int): int { if x < 0 then -x else x }

/* helper modified by LLM (iteration 5): Euclidean gcd helper with proper decreases clause and handling zero-zero */
function GcdRec(x: int, y: int): int
  requires x >= 0 && y >= 0
  decreases x + y
  ensures result > 0 && x % result == 0 && y % result == 0 && (forall d :: d > 0 && x % d == 0 && y % d == 0 ==> d <= result)
{
  if y == 0 then if x == 0 then 1 else x else GcdRec(y, x % y)
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
  /* code modified by LLM (iteration 5): compute gcd using Abs and GcdRec */
  var x := Abs(a);
  var y := Abs(b);
  result := GcdRec(x, y);
}
// </vc-code>
