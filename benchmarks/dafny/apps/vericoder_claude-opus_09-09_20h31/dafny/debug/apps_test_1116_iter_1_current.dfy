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

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
method solve(r: int, b: int, k: int) returns (result: string)
  requires ValidInput(r, b, k)
  ensures result == (if CanAvoidConsecutive(r, b, k) then "OBEY" else "REBEL")
// </vc-spec>
// <vc-code>
{
  var maxConsec := MaxConsecutiveSameColor(r, b);
  if maxConsec < k {
    result := "OBEY";
  } else {
    result := "REBEL";
  }
}
// </vc-code>

