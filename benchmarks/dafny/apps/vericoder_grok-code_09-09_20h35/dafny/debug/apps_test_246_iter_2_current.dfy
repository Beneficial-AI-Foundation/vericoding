function SumOfDigits(x: int): int
  requires x >= 0
  decreases x
{
  if x == 0 then 0
  else (x % 10) + SumOfDigits(x / 10)
}

function Check(x: int, s: int): bool
  requires x >= 0
{
  x - SumOfDigits(x) >= s
}

// <vc-helpers>
// <vc-helpers>

// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: int) returns (result: int)
  requires n >= 1 && s >= 1
  ensures result >= 0
  ensures result <= n
  ensures result == |set x | 1 <= x <= n && Check(x, s)|
// </vc-spec>
// <vc-code>
{
  var result: int := 0;
  for i := 1 to n
    invariant 0 <= result <= i - 1;
    invariant result == |set x: int | 1 <= x < i && Check(x, s)|
  {
    if Check(i, s) {
      result := result + 1;
    }
  }
}
// </vc-code>

