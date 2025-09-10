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
predicate method ValidDigitSum(x: int, s: int)
  requires x >= 0
{
  x - SumOfDigits(x) >= s
}
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
  var count := 0;
  var x := 1;
  while x <= n
    invariant count == |set k | 1 <= k < x && ValidDigitSum(k, s)|
    invariant x <= n + 1
  {
    if ValidDigitSum(x, s)
    {
      count := count + 1;
    }
    x := x + 1;
  }
  return count;
}
// </vc-code>

