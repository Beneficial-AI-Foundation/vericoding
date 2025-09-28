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
lemma ProductOfDigitsNonNegative(x: int)
  requires x >= 0
  ensures ProductOfDigits(x) >= 0
{
  if x == 0 {
    assert ProductOfDigits(x) == 1;
  } else if x < 10 {
    assert ProductOfDigits(x) == x;
  } else {
    ProductOfDigitsNonNegative(x / 10);
    assert ProductOfDigits(x) == (x % 10) * ProductOfDigits(x / 10);
  }
}

lemma ProductOfDigitsOfOne()
  ensures ProductOfDigits(1) == 1
{
}

lemma MaxProductInRangeProperties(n: int)
  requires n >= 1
  ensures MaxProductOfDigitsInRange(n) >= 1
  ensures forall k :: 1 <= k <= n ==> ProductOfDigits(k) <= MaxProductOfDigitsInRange(n)
  ensures exists k :: 1 <= k <= n && ProductOfDigits(k) == MaxProductOfDigitsInRange(n)
{
  if n == 1 {
    assert ProductOfDigits(1) == 1;
    assert MaxProductOfDigitsInRange(1) == 1;
  } else {
    MaxProductInRangeProperties(n - 1);
    var current := ProductOfDigits(n);
    var rest := MaxProductOfDigitsInRange(n - 1);
    
    assert rest >= 1;
    ProductOfDigitsNonNegative(n);
    
    if current > rest {
      assert MaxProductOfDigitsInRange(n) == current;
      // Since current > rest and rest >= 1, we have current > 1, so current >= 1
      assert current > rest >= 1;
      assert ProductOfDigits(n) == MaxProductOfDigitsInRange(n);
    } else {
      assert MaxProductOfDigitsInRange(n) == rest;
      assert MaxProductOfDigitsInRange(n) >= 1;
      var k :| 1 <= k <= n - 1 && ProductOfDigits(k) == rest;
      assert 1 <= k <= n && ProductOfDigits(k) == MaxProductOfDigitsInRange(n);
    }
    
    // Prove the universal property
    forall k | 1 <= k <= n
      ensures ProductOfDigits(k) <= MaxProductOfDigitsInRange(n)
    {
      if k == n {
        assert ProductOfDigits(k) == current;
        if current > rest {
          assert MaxProductOfDigitsInRange(n) == current;
        } else {
          assert MaxProductOfDigitsInRange(n) == rest;
          assert current <= rest;
        }
      } else {
        assert 1 <= k <= n - 1;
        assert ProductOfDigits(k) <= rest;
        assert rest <= MaxProductOfDigitsInRange(n);
      }
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
  result := ProductOfDigits(1);
  var i := 2;
  
  assert result == 1;
  assert result == MaxProductOfDigitsInRange(1);
  
  while i <= n
    invariant 2 <= i <= n + 1
    invariant result == MaxProductOfDigitsInRange(i - 1)
    invariant result >= 1
    invariant forall k :: 1 <= k < i ==> ProductOfDigits(k) <= result
    invariant exists k :: 1 <= k < i && ProductOfDigits(k) == result
  {
    MaxProductInRangeProperties(i - 1);
    
    var current := ProductOfDigits(i);
    
    if current > result {
      result := current;
    }
    
    assert result == (if current > MaxProductOfDigitsInRange(i - 1) then current else MaxProductOfDigitsInRange(i - 1));
    assert result == MaxProductOfDigitsInRange(i);
    
    MaxProductInRangeProperties(i);
    
    i := i + 1;
  }
  
  assert i == n + 1;
  assert result == MaxProductOfDigitsInRange(n);
  MaxProductInRangeProperties(n);
}
// </vc-code>

