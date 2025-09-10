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
lemma MaxProductOfDigitsInRangeDecreases(n: int)
  requires n >= 1
  ensures MaxProductOfDigitsInRange(n) >= MaxProductOfDigitsInRange(n - 1)
  decreases n
{
  if n > 1 {
    MaxProductOfDigitsInRangeDecreases(n - 1);
    var current := ProductOfDigits(n);
    assert MaxProductOfDigitsInRange(n) == (if current > MaxProductOfDigitsInRange(n - 1) then current else MaxProductOfDigitsInRange(n - 1));
  }
}

lemma ProductOfDigitsNonNegative(x: int)
  requires x >= 0
  ensures ProductOfDigits(x) >= 1
  decreases x
{
  if x >= 10 {
    ProductOfDigitsNonNegative(x / 10);
    assert x % 10 >= 1;
  } else if x == 0 {
  } else {
  }
}

lemma MaxProductOfDigitsInRangeProperty(n: int, k: int)
  requires n >= 1
  requires 1 <= k <= n
  ensures ProductOfDigits(k) <= MaxProductOfDigitsInRange(n)
  decreases n
{
  if n == k {
    assert ProductOfDigits(k) == ProductOfDigits(n);
    var current := ProductOfDigits(n);
    assert MaxProductOfDigitsInRange(n) >= current;
  } else {
    MaxProductOfDigitsInRangeDecreases(n);
    MaxProductOfDigitsInRangeProperty(n - 1, k);
  }
}

lemma MaxProductOfDigitsInRangeContainsAtLeastOne(n: int)
  requires n >= 1
  ensures exists k :: 1 <= k <= n && ProductOfDigits(k) == MaxProductOfDigitsInRange(n)
  decreases n
{
  if n == 1 {
  } else {
    var current := ProductOfDigits(n);
    MaxProductOfDigitsInRangeContainsAtLeastOne(n - 1);
    if current > MaxProductOfDigitsInRange(n - 1) {
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
  if n == 1 {
    result := 1;
  } else {
    ProductOfDigitsNonNegative(n);
    var current := ProductOfDigits(n);
    var rest := solve(n - 1);
    assert rest == MaxProductOfDigitsInRange(n - 1);
    if current > rest {
      result := current;
      MaxProductOfDigitsInRangeContainsAtLeastOne(n - 1);
    } else {
      result := rest;
      MaxProductOfDigitsInRangeContainsAtLeastOne(n);
    }
  }
}
// </vc-code>

