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
  ensures ProductOfDigits(x) >= 0
  ensures ProductOfDigits(x) >= 1 <==> (x == 0 || forall d :: d in DigitsOf(x) ==> d > 0)
{
  if x == 0 {
    assert ProductOfDigits(x) == 1;
    assert DigitsOf(x) == {0};
    assert ProductOfDigits(x) >= 1;
  } else if x < 10 {
    assert ProductOfDigits(x) == x;
    assert DigitsOf(x) == {x};
    if x > 0 {
      assert forall d :: d in DigitsOf(x) ==> d > 0;
      assert ProductOfDigits(x) >= 1;
    } else {
      assert x == 0; // contradiction since we're in else branch
    }
  } else {
    ProductOfDigitsPositive(x / 10);
    var lastDigit := x % 10;
    var restDigits := x / 10;
    assert ProductOfDigits(x) == lastDigit * ProductOfDigits(restDigits);
    assert DigitsOf(x) == {lastDigit} + DigitsOf(restDigits);
    
    if ProductOfDigits(x) >= 1 {
      if lastDigit == 0 {
        assert ProductOfDigits(x) == 0;
        assert false; // contradiction
      } else {
        assert lastDigit > 0;
        assert ProductOfDigits(restDigits) >= 1;
        assert forall d :: d in DigitsOf(restDigits) ==> d > 0;
        assert forall d :: d in DigitsOf(x) ==> d > 0;
      }
    } else {
      if lastDigit == 0 {
        assert ProductOfDigits(x) == 0;
        assert !(forall d :: d in DigitsOf(x) ==> d > 0);
      } else {
        assert ProductOfDigits(restDigits) == 0;
        assert !(forall d :: d in DigitsOf(restDigits) ==> d > 0);
        assert !(forall d :: d in DigitsOf(x) ==> d > 0);
      }
    }
  }
}

function DigitsOf(x: int): set<int>
  requires x >= 0
{
  if x < 10 then {x}
  else {x % 10} + DigitsOf(x / 10)
}

lemma ProductOfDigitsNonNegative(x: int)
  requires x >= 0
  ensures ProductOfDigits(x) >= 0
{
  if x == 0 {
  } else if x < 10 {
  } else {
    ProductOfDigitsNonNegative(x / 10);
  }
}

lemma MaxProductOfDigitsInRangeProperties(n: int)
  requires n >= 1
  ensures MaxProductOfDigitsInRange(n) >= 1
  ensures forall k :: 1 <= k <= n ==> ProductOfDigits(k) <= MaxProductOfDigitsInRange(n)
  ensures exists k :: 1 <= k <= n && ProductOfDigits(k) == MaxProductOfDigitsInRange(n)
{
  ProductOfDigitsNonNegative(n);
  if n == 1 {
    ProductOfDigitsNonNegative(1);
    assert ProductOfDigits(1) == 1;
    assert MaxProductOfDigitsInRange(1) == 1;
  } else {
    MaxProductOfDigitsInRangeProperties(n - 1);
    var current := ProductOfDigits(n);
    var rest := MaxProductOfDigitsInRange(n - 1);
    ProductOfDigitsNonNegative(n);
    assert rest >= 1;
    if current > rest {
      assert MaxProductOfDigitsInRange(n) == current;
      assert current > rest && rest >= 1;
      assert current >= 1;
    } else {
      assert MaxProductOfDigitsInRange(n) == rest;
      assert rest >= 1;
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

