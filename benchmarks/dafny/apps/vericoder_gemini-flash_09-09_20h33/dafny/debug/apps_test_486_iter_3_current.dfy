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
    // ProductOfDigits(n) is >= 1 for n >= 1
    // if ProductOfDigits(n) is 0, it means n has a digit 0, 
    // and if so, it's irrelevant to the max
    // if ProductOfDigits(n) is > 0, then the result is max(ProductOfDigits(n), MaxProductOfDigitsInRange(n-1)) which is > 0.
    // However, ProductOfDigits(n) won't be 0 if n >= 1.
    // Only ProductOfDigits(0) is 1. If x > 0, then ProductOfDigits(x) >= 1 if no digit is 0.
    // If x contains digit 0, then ProductOfDigits(x) can be 0.
    // For example ProductOfDigits(10) is 0. ProductOfDigits(20) is 0.
    // If MaxProductOfDigitsInRange returns 0, then it is an incorrect max.
    // Product of digits can only be 0 if one of its digits is 0.
    // The problem statement functions ProductOfDigits and MaxProductOfDigitsInRange are copied directly.
    // A product of positive digits should be positive.
    // A `ProductOfDigits` that can return `0` for `x >= 1` (e.g. `10, 20`) is potentially problematic for "Max" calculation
    // because `MaxProductOfDigitsInRange` might return `0` if all elements `ProductOfDigits(k)` are `0`.
    // However, the problem statement provides fixed definitions for `ProductOfDigits` and `MaxProductOfDigitsInRange`
    // which should be taken as given. If n has a 0 digit, say n=10, ProductOfDigits(10) = 0.
    // If all k in 1..n had 0 as product of digits, then MaxProductOfDigitsInRange(n) would be 0.
    // But ProductOfDigits(1) = 1, so MaxProductOfDigitsInRange(n) must be >= 1 for n >= 1.
    // This implies that it cannot return 0.
    assert ProductOfDigits(n) >= 0; // True by definition, as x >= 0 inputs.
    // If ProductOfDigits(n) is 0, and MaxProductOfDigitsInRange(n-1) is >= 1, then MaxProductOfDigitsInRange(n) will be >= 1.
    // If MaxProductOfDigitsInRange(n-1) is 0 and ProductOfDigits(n) is >= 1, then MaxProductOfDigitsInRange(n) will be >= 1.
    // The base case `MaxProductOfDigitsInRange(1)` is `ProductOfDigits(1)`, which is `1`.
    // So the inductive step will always propagate `>= 1`.
  }
}

lemma MaxProductOfDigitsInRange_is_max(n: int)
  requires n >= 1
  ensures forall k :: 1 <= k <= n ==> ProductOfDigits(k) <= MaxProductOfDigitsInRange(n)
{
  if n == 1 {
    assert ProductOfDigits(1) <= MaxProductOfDigitsInRange(1); // 1 <= 1
  } else {
    MaxProductOfDigitsInRange_is_max(n - 1);
    // Inductive hypothesis: forall k :: 1 <= k <= n-1 ==> ProductOfDigits(k) <= MaxProductOfDigitsInRange(n-1)

    // Case 1: ProductOfDigits(n) is the new maximum.
    if ProductOfDigits(n) > MaxProductOfDigitsInRange(n - 1) {
      assert MaxProductOfDigitsInRange(n) == ProductOfDigits(n);
      // We need to show ProductOfDigits(k) <= ProductOfDigits(n) for all k in 1..n.
      // For k=n, it's trivial.
      // For k in 1..n-1, we know ProductOfDigits(k) <= MaxProductOfDigitsInRange(n-1).
      // Since MaxProductOfDigitsInRange(n-1) < ProductOfDigits(n), it follows that
      // ProductOfDigits(k) <= MaxProductOfDigitsInRange(n-1) < ProductOfDigits(n).
      // Thus, ProductOfDigits(k) <= MaxProductOfDigitsInRange(n) for all k in 1..n.
    } else { // Case 2: MaxProductOfDigitsInRange(n-1) remains the maximum.
      assert MaxProductOfDigitsInRange(n) == MaxProductOfDigitsInRange(n - 1);
      // We need to show ProductOfDigits(k) <= MaxProductOfDigitsInRange(n-1) for all k in 1..n.
      // For k=n, we know ProductOfDigits(n) <= MaxProductOfDigitsInRange(n-1), which is what we need.
      // For k in 1..n-1, we know ProductOfDigits(k) <= MaxProductOfDigitsInRange(n-1) by IH.
      // Thus, ProductOfDigits(k) <= MaxProductOfDigitsInRange(n) for all k in 1..n.
    }
  }
}

lemma MaxProductOfDigitsInRange_exists_k(n: int)
  requires n >= 1
  ensures exists k :: 1 <= k <= n && ProductOfDigits(k) == MaxProductOfDigitsInRange(n)
{
  if n == 1 {
    // k = 1 satisfies the condition: ProductOfDigits(1) == MaxProductOfDigitsInRange(1)
    assert ProductOfDigits(1) == 1;
    assert MaxProductOfDigitsInRange(1) == 1;
  } else {
    if ProductOfDigits(n) >= MaxProductOfDigitsInRange(n - 1) {
      // In this case, MaxProductOfDigitsInRange(n) is ProductOfDigits(n).
      // So k = n satisfies the condition.
      assert MaxProductOfDigitsInRange(n) == ProductOfDigits(n);
      assert exists k :: 1 <= k <= n && ProductOfDigits(k) == MaxProductOfDigitsInRange(n);
    } else {
      // In this case, MaxProductOfDigitsInRange(n) is MaxProductOfDigitsInRange(n - 1).
      // By induction hypothesis, there exists j in 1..n-1 such that ProductOfDigits(j) == MaxProductOfDigitsInRange(n-1).
      MaxProductOfDigitsInRange_exists_k(n - 1);
      // Let that j be k'. Then 1 <= k' <= n-1, and ProductOfDigits(k') == MaxProductOfDigitsInRange(n-1).
      // Since MaxProductOfDigitsInRange(n) == MaxProductOfDigitsInRange(n-1),
      // we have ProductOfDigits(k') == MaxProductOfDigitsInRange(n).
      // And 1 <= k' <= n-1 implies 1 <= k' <= n.
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

