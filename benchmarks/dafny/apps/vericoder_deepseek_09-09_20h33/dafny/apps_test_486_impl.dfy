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
    // We need to show result == MaxProductOfDigitsInRange(n)
    assert MaxProductOfDigitsInRange(n) == (if current > MaxProductOfDigitsInRange(n - 1) 
                                          then current else MaxProductOfDigitsInRange(n - 1));
    assert result == (if current > rest then current else rest);
    
    // The other postconditions follow from the lemmas
    MaxProductOfDigitsInRangeProperty(n, n);
    MaxProductOfDigitsInRangeContainsAtLeastOne(n);
  }
}
// </vc-code>

