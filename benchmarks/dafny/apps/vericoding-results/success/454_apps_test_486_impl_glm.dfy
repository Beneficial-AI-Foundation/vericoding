function ProductOfDigits(x: int): int
  requires x >= 0
{
  if x == 0 then 1
  else if x < 10 then x
  else (x % 10) * ProductOfDigits(x / 10)
}

function MaxProductOfDigitsInRange(n: int): int
  requires n >= 1
{
  if n == 1 then 1
  else
    var current := ProductOfDigits(n);
    var rest := MaxProductOfDigitsInRange(n - 1);
    if current > rest then current else rest
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
  requires n >= 1
  ensures result == MaxProductOfDigitsInRange(n)
  ensures result >= 1
  ensures forall k :: 1 <= k <= n ==> ProductOfDigits(k) <= result
  ensures exists k :: 1 <= k <= n && ProductOfDigits(k) == result
// </vc-spec>
// <vc-code>
{
  var max := 1;
  var i := 1;
  while i <= n
    invariant 1 <= i <= n+1
    invariant max == (if i == 1 then 1 else MaxProductOfDigitsInRange(i-1))
    invariant max >= 1
    invariant forall k :: 1 <= k < i ==> ProductOfDigits(k) <= max
    invariant i > 1 ==> exists k :: 1 <= k < i && ProductOfDigits(k) == max
  {
    var p := ProductOfDigits(i);
    if p > max {
      max := p;
    }
    i := i + 1;
  }
  result := max;
}
// </vc-code>

