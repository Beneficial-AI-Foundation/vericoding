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
    assert ProductOfDigits(x) == x;
  } else {
    ProductOfDigitsPositive(x / 10);
  }
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
    
    if current > rest {
      assert MaxProductOfDigitsInRange(n) == current;
      assert ProductOfDigits(n) == MaxProductOfDigitsInRange(n);
    } else {
      assert MaxProductOfDigitsInRange(n) == rest;
      var k :| 1 <= k <= n - 1 && ProductOfDigits(k) == rest;
      assert 1 <= k <= n && ProductOfDigits(k) == MaxProductOfDigitsInRange(n);
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
  result := 1;
  var i := 1;
  
  while i <= n
    invariant 1 <= i <= n + 1
    invariant result == MaxProductOfDigitsInRange(i - 1)
    invariant result >= 1
    invariant forall k :: 1 <= k < i ==> ProductOfDigits(k) <= result
    invariant exists k :: 1 <= k < i && ProductOfDigits(k) == result
  {
    var current := ProductOfDigits(i);
    ProductOfDigitsPositive(i);
    
    if current > result {
      result := current;
    }
    
    assert result == (if current > MaxProductOfDigitsInRange(i - 1) then current else MaxProductOfDigitsInRange(i - 1));
    assert result == MaxProductOfDigitsInRange(i);
    
    i := i + 1;
  }
  
  assert i == n + 1;
  assert result == MaxProductOfDigitsInRange(n);
  MaxProductInRangeProperties(n);
}
// </vc-code>

