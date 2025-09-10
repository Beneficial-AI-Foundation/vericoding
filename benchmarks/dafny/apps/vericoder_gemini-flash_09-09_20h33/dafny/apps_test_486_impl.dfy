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
// The functions ProductOfDigits and MaxProductOfDigitsInRange are defined in the preamble,
// so they should not be redefined here.
// Instead, we only define the lemmas that depend on these functions.

lemma MaxProductOfDigitsInRange_at_least_one(n: int)
  requires n >= 1
  ensures MaxProductOfDigitsInRange(n) >= 1
{
  if n == 1 {
    assert ProductOfDigits(1) == 1; // ProductOfDigits(1) == 1
  } else {
    MaxProductOfDigitsInRange_at_least_one(n - 1);
    // Inductive step: MaxProductOfDigitsInRange(n-1) >= 1.
    // ProductOfDigits(n) >= 0 (as per the definition).
    // If ProductOfDigits(n) is 0 (e.g., n=10), then max(0, MaxProductOfDigitsInRange(n-1)) = MaxProductOfDigitsInRange(n-1) >= 1.
    // If ProductOfDigits(n) > 0 (e.g., n=12), then max(ProductOfDigits(n), MaxProductOfDigitsInRange(n-1)) >= 1.
    // In all cases, MaxProductOfDigitsInRange(n) >= 1.
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
    assert ProductOfDigits(1) == 1; // ProductOfDigits(1) == 1
    assert MaxProductOfDigitsInRange(1) == 1; // MaxProductOfDigitsInRange(1) == 1
  } else {
    if ProductOfDigits(n) >= MaxProductOfDigitsInRange(n - 1) {
      // In this case, MaxProductOfDigitsInRange(n) is ProductOfDigits(n).
      // So k = n satisfies the condition.
      assert MaxProductOfDigitsInRange(n) == ProductOfDigits(n);
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

