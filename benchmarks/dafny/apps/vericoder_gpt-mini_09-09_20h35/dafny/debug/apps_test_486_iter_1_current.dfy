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
// No helpers needed.
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
  var i := 1;
  result := ProductOfDigits(1);
  while i < n
    invariant 1 <= i <= n
    invariant result == MaxProductOfDigitsInRange(i)
    invariant forall k :: 1 <= k <= i ==> ProductOfDigits(k) <= result
    invariant exists k :: 1 <= k <= i && ProductOfDigits(k) == result
  {
    var next := i + 1;
    var t := ProductOfDigits(next);
    var old := result;
    if t > result {
      result := t;
    }
    // Show MaxProductOfDigitsInRange(next) matches the updated result
    assert MaxProductOfDigitsInRange(next) == (if t > old then t else MaxProductOfDigitsInRange(i));
    assert MaxProductOfDigitsInRange(next) == (if t > old then t else old);
    i := next;
  }
  // At loop exit i == n and invariants give the postconditions
}
// </vc-code>

