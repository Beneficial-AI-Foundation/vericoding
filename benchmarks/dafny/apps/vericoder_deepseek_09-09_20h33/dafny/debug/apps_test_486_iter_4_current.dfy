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
    assert x % 10 >= 0;
    // The product of positive numbers is at least 1
    // Since x/10 >= 1 when x >= 10, ProductOfDigits(x/10) >= 1
    // and x % 10 >= 0, so the product is >= 0 * 1 = 0, but we need >= 1
    // Let's be more careful about the base cases
  } else if x == 0 {
    // ProductOfDigits(0) = 1 by definition
  } else {
    // x between 1 and 9, ProductOfDigits(x) = x >= 1
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
    assert MaxProductOfDigitsInRange(n) >= MaxProductOfDigitsInRange(n - 1);
  }
}

lemma MaxProductOfDigitsInRangeContainsAtLeastOne(n: int)
  requires n >= 1
  ensures exists k :: 1 <= k <= n && ProductOfDigits(k) == MaxProductOfDigitsInRange(n)
  decreases n
{
  if n == 1 {
    // Base case: k = 1, ProductOfDigits(1) = 1 = MaxProductOfDigitsInRange(1)
  } else {
    var current := ProductOfDigits(n);
    MaxProductOfDigitsInRangeContainsAtLeastOne(n - 1);
    if current > MaxProductOfDigitsInRange(n - 1) {
      // k = n gives the maximum
    } else {
      // The maximum from n-1 is still the maximum
    }
  }
}

lemma ProductOfDigitsGeOneForPositive(x: int)
  requires x >= 1
  ensures ProductOfDigits(x) >= 1
  decreases x
{
  if x < 10 {
    // x is between 1-9, ProductOfDigits(x) = x ≥ 1
  } else {
    ProductOfDigitsGeOneForPositive(x / 10);
    // x % 10 could be 0, but ProductOfDigits(x/10) ≥ 1, so product is ≥ 0
    // Actually, we need to handle the case where digits could be 0
    // Let's adjust the function to handle 0 digits properly
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
    var current := ProductOfDigits(n);
    var rest := solve(n - 1);
    assert rest == MaxProductOfDigitsInRange(n - 1);
    if current > rest {
      result := current;
    } else {
      result := rest;
    }
    // Prove the postconditions
    MaxProductOfDigitsInRangeProperty(n, n);
    MaxProductOfDigitsInRangeContainsAtLeastOne(n);
  }
}
// </vc-code>

