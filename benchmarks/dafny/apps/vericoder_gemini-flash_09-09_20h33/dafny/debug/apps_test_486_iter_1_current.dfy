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
  if n == 1 then ProductOfDigits(1)
  else
    var current := ProductOfDigits(n);
    var rest := MaxProductOfDigitsInRange(n - 1);
    if current > rest then current else rest
}

lemma MaxProductOfDigitsInRange_at_least_one(n: int)
  requires n >= 1
  ensures MaxProductOfDigitsInRange(n) >= 1
{
  if n == 1 {
    assert ProductOfDigits(1) == 1;
  } else {
    MaxProductOfDigitsInRange_at_least_one(n - 1);
    assert MaxProductOfDigitsInRange(n - 1) >= 1;
    assert ProductOfDigits(n) >= 1;
  }
}

lemma MaxProductOfDigitsInRange_is_max(n: int)
  requires n >= 1
  ensures forall k :: 1 <= k <= n ==> ProductOfDigits(k) <= MaxProductOfDigitsInRange(n)
{
  if n == 1 {
  } else {
    MaxProductOfDigitsInRange_is_max(n - 1);
    if ProductOfDigits(n) > MaxProductOfDigitsInRange(n - 1) {
    } else {
    }
  }
}

lemma MaxProductOfDigitsInRange_exists_k(n: int)
  requires n >= 1
  ensures exists k :: 1 <= k <= n && ProductOfDigits(k) == MaxProductOfDigitsInRange(n)
{
  if n == 1 {
  } else {
    if ProductOfDigits(n) >= MaxProductOfDigitsInRange(n - 1) {
    } else {
      MaxProductOfDigitsInRange_exists_k(n - 1);
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
  MaxProductOfDigitsInRange_at_least_one(n);
  MaxProductOfDigitsInRange_is_max(n);
  MaxProductOfDigitsInRange_exists_k(n);
  return MaxProductOfDigitsInRange(n);
}
// </vc-code>

