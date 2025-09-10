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
lemma ProductOfDigitsPositive(x: int)
  requires x >= 0
  ensures ProductOfDigits(x) >= 1
{
  if x == 0 {
  } else if x < 10 {
  } else {
    ProductOfDigitsPositive(x / 10);
  }
}

lemma MaxProductOfDigitsInRangeProperties(n: int)
  requires n >= 1
  ensures MaxProductOfDigitsInRange(n) >= 1
  ensures forall k :: 1 <= k <= n ==> ProductOfDigits(k) <= MaxProductOfDigitsInRange(n)
  ensures exists k :: 1 <= k <= n && ProductOfDigits(k) == MaxProductOfDigitsInRange(n)
{
  ProductOfDigitsPositive(n);
  if n == 1 {
    ProductOfDigitsPositive(1);
  } else {
    MaxProductOfDigitsInRangeProperties(n - 1);
    var current := ProductOfDigits(n);
    var rest := MaxProductOfDigitsInRange(n - 1);
    if current > rest {
    } else {
    }
  }
}
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
  MaxProductOfDigitsInRangeProperties(n);
  result := MaxProductOfDigitsInRange(n);
}
// </vc-code>

