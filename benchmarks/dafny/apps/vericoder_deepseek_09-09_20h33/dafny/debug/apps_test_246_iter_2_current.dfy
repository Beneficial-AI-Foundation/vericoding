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
lemma CheckMonotonic(x: int, s: int)
  requires x >= 0 && s >= 1
  ensures Check(x, s) ==> forall y :: x <= y ==> Check(y, s)
{
  // Since SumOfDigits grows slower than x itself, once Check becomes true for x,
  // it remains true for all larger numbers
  if Check(x, s) {
    var y := x + 1;
    assert Check(y, s) by {
      calc {
        y - SumOfDigits(y);
        == (x + 1) - SumOfDigits(x + 1);
        >= (x + 1) - (SumOfDigits(x) + 1); // Adding 1 can increase sum of digits by at most 1
        == x - SumOfDigits(x);
        >= s;
      }
    }
  }
}

predicate IsLowerBound(n: int, s: int, candidate: int)
{
  candidate >= 0 && candidate <= n + 1 &&
  (candidate == 0 || Check(candidate, s)) &&
  (candidate == n + 1 || !Check(candidate + 1, s))
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
  if n == 0 {
    result := 0;
    return;
  }
  
  var low := 0;
  var high := n + 1;
  
  while low + 1 < high
    invariant 0 <= low < high <= n + 1
    invariant IsLowerBound(n, s, low)
    invariant IsLowerBound(n, s, high)
    decreases high - low
  {
    var mid := (low + high) / 2;
    
    if Check(mid, s) {
      low := mid;
    } else {
      high := mid;
    }
  }
  
  // All numbers from low to n satisfy Check(x, s)
  result := n - low;
}
// </vc-code>

