// <vc-preamble>
function gcd(a: int, b: int): int
  requires a > 0 && b >= 0
  decreases b
{
  if b == 0 then a else gcd(b, a % b)
}

predicate ValidInput(r: int, b: int, k: int)
{
  r > 0 && b > 0 && k > 0
}

function MaxConsecutiveSameColor(r: int, b: int): int
  requires r > 0 && b > 0
{
  var a := if r <= b then r else b;
  var b_val := if r <= b then b else r;
  var n := gcd(a, b_val);
  -((n - b_val) / a)
}

predicate CanAvoidConsecutive(r: int, b: int, k: int)
  requires ValidInput(r, b, k)
{
  MaxConsecutiveSameColor(r, b) < k
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Simplified logic and removed the unnecessary `MaxConsecutiveSameColorPositive` helper. The `MaxConsecutiveSameColor` function, which was commented out, is the correct implementation and now serves as the single source for this calculation, directly using `gcd(r, b)`. No helper functions are needed, so this section is empty. */
// </vc-helpers>

// <vc-spec>
method solve(r: int, b: int, k: int) returns (result: string)
  requires ValidInput(r, b, k)
  ensures result == (if CanAvoidConsecutive(r, b, k) then "OBEY" else "REBEL")
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Used the predicate 'CanAvoidConsecutive' to determine the result. */
{
  if CanAvoidConsecutive(r, b, k) {
    result := "OBEY";
  } else {
    result := "REBEL";
  }
}
// </vc-code>
