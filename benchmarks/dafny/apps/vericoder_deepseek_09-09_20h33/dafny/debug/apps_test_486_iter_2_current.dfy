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
  }
}

lemma ProductOfDigitsNonNegative(x: int)
  requires x >= 0
  ensures ProductOfDigits(x) >= 1
  decreases x
{
  if x >= 10 {
    ProductOfDigitsNonNegative(x / 10);
    // ProductOfDigits(x) = (x % 10) * ProductOfDigits(x / 10)
    // x % 10 >= 1 when x >= 10, and ProductOfDigits(x / 10) >= 1
  } else if x == 0 {
    // ProductOfDigits(0) = 1
  } else {
    // x is between 1 and 9, ProductOfDigits(x) = x >= 1
  }
}

lemma MaxProductOfDigitsInRangeProperty(n: int, k: int)
  requires n >= 1
  requires 1 <= k <= n
  ensures ProductOfDigits(k) <= MaxProductOfDigitsInRange(n)
  decreases n
{
  if n == k {
    // Base case: when n equals k, MaxProductOfDigitsInRange(n) considers ProductOfDigits(k)
  } else {
    MaxProductOfDigitsInRangeDecreases(n);
    assert MaxProductOfDigitsInRange(n) >= MaxProductOfDigitsInRange(n - 1);
    MaxProductOfDigitsInRangeProperty(n - 1, k);
    assert MaxProductOfDigitsInRange(n - 1) >= ProductOfDigits(k);
  }
}

lemma MaxProductOfDigitsInRangeContainsAtLeastOne(n: int)
  requires n >= 1
  ensures exists k :: 1 <= k <= n && ProductOfDigits(k) == MaxProductOfDigitsInRange(n)
  decreases n
{
  if n == 1 {
    // For n=1, k=1 satisfies ProductOfDigits(1)=1 = MaxProductOfDigitsInRange(1)
  } else {
    var current := ProductOfDigits(n);
    var rest_max := MaxProductOfDigitsInRange(n - 1);
    if current > rest_max {
      // n itself achieves the maximum
    } else {
      // The maximum comes from the recursive call
      MaxProductOfDigitsInRangeContainsAtLeastOne(n - 1);
    }
  }
}
// </vc-helpers>
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
    assert rest == MaxProductOfDigitsInRange(n - 1) by {
      MaxProductOfDigitsInRangeDecreases(n);
    }
    if current > rest {
      result := current;
    } else {
      result := rest;
    }
  }
}
// </vc-code>

