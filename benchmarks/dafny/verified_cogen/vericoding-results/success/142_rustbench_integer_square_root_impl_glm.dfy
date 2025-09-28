// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added body to lemma to provide actual proof */
function Square(x: int): int { x * x }

lemma SquareIncreasing(x: int, y: int)
  requires 0 <= x <= y
  ensures Square(x) <= Square(y)
{
  calc {
    Square(y) - Square(x);
    ==  { assert Square(y) - Square(x) == (y-x)*(y+x); }
    (y-x)*(y+x);
    >= { assert 0 <= y-x; assert 0 <= y+x; }
    0;
  }
}
// </vc-helpers>

// <vc-spec>
method IntegerSquareRoot(n: int) returns (result: int)
    requires n >= 1
    ensures 0 <= result * result
    ensures result * result <= n
    ensures n < (result + 1) * (result + 1)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): wrapped entire method body in braces to fix compilation error */
{
  var low, high := 0, n+1;
  while low + 1 < high
    invariant 0 <= low < high
    invariant Square(low) <= n
    invariant n < Square(high)
    decreases high - low
  {
    var mid := (low + high) / 2;
    if (Square(mid) <= n) {
      low := mid;
    } else {
      high := mid;
    }
  }
  result := low;
}
// </vc-code>
