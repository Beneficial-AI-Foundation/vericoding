// <vc-preamble>
predicate ValidInput(n: int, a: int, b: int, p: int, q: int) {
  n > 0 && a > 0 && b > 0 && p > 0 && q > 0
}

function gcd(a: int, b: int): int
  requires a > 0 && b >= 0
  ensures gcd(a, b) > 0
  decreases b
{
  if b == 0 then a else gcd(b, a % b)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Add ensures clauses to FindMax for determinism and positive return values */
function FindMax(a: int, b: int, p: int, q: int): int
  requires a > 0 && b > 0 && p > 0 && q > 0
  ensures FindMax(a, b, p, q) >= 0
{
  if (a / p + b / q) > (a / q + b / p) then (a / p + b / q) else (a / q + b / p)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int, p: int, q: int) returns (result: int)
  requires ValidInput(n, a, b, p, q)
  ensures result >= 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Removed direct multiplication with max_k and corrected the logic to find the maximum possible value for x + y */
{
  var max_val := 0;
  if p * q != 0 { // Avoid division by zero, though inputs ensure this.
    var val1 := (a / p) + (b / q);
    var val2 := (a / q) + (b / p);
    max_val := if val1 > val2 then val1 else val2;
  }
  
  result := 0;
  var k := n / gcd(p,q);
  
  if (k > 0) {
    result := k * max_val;
  }
}
// </vc-code>
