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
lemma SumOfDigitsNonNegative(x: int)
  requires x >= 0
  ensures SumOfDigits(x) >= 0
  decreases x
{
  if x == 0 {
  } else {
    SumOfDigitsNonNegative(x / 10);
  }
}

lemma SumOfDigitsUpperBound(x: int)
  requires x >= 0
  ensures SumOfDigits(x) <= x
  decreases x
{
  if x == 0 {
  } else {
    SumOfDigitsUpperBound(x / 10);
  }
}

lemma CheckDecidable(x: int, s: int)
  requires x >= 0 && s >= 1
  ensures Check(x, s) == (x - SumOfDigits(x) >= s)
{
}

lemma SetEquality(n: int, s: int)
  requires n >= 1 && s >= 1
  ensures (set y | 1 <= y < n + 1 && Check(y, s)) == (set y | 1 <= y <= n && Check(y, s))
{
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
  result := 0;
  var count := 0;
  var x := 1;
  
  while x <= n
    invariant 1 <= x <= n + 1
    invariant count == |set y | 1 <= y < x && Check(y, s)|
    invariant count >= 0
  {
    SumOfDigitsNonNegative(x);
    SumOfDigitsUpperBound(x);
    
    if Check(x, s) {
      count := count + 1;
    }
    
    x := x + 1;
  }
  
  result := count;
  
  assert x == n + 1;
  assert count == |set y | 1 <= y < n + 1 && Check(y, s)|;
  SetEquality(n, s);
  assert |set y | 1 <= y < n + 1 && Check(y, s)| == |set y | 1 <= y <= n && Check(y, s)|;
}
// </vc-code>

