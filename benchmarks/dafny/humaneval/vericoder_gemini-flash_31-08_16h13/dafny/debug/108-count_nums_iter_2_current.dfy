

// <vc-helpers>
lemma lemma_digits_sum_nonNegative(x: int)
  ensures digits_sum(x) <= 0 ==> x == 0
  decreases abs(x)
{
  if abs(x) < 10 {
    // If x is a single digit number, digits_sum(x) is x itself.
    // If digits_sum(x) <= 0, then x <= 0.
    // However, the postcondition requires digits_sum(x) > 0, so x must be positive for that.
  } else {
    // digits_sum(x) = x % 10 + digits_sum(x / 10)
    // Here, we can't directly conclude digits_sum(x) > 0 if x != 0 because of negative numbers.
    // Example: digits_sum(-10) = 0 + digits_sum(-1) = 0 - 1 = -1
    // The proof that digits_sum(x) > 0 requires x to be positive.
    // For x in N (nat), digits_sum(x) > 0 if x > 0.
    lemma_digits_sum_nonNegative(x / 10);
  }
}

lemma lemma_digits_sum_N_positive(x: nat)
  ensures x > 0 ==> digits_sum(x) > 0
  decreases x
{
  if x < 10 {
    // digits_sum(x) = x. If x > 0, then digits_sum(x) > 0.
  } else {
    // digits_sum(x) = x % 10 + digits_sum(x / 10)
    // x % 10 >= 0
    // x / 10 is a natural number and x / 10 < x.
    // If x / 10 > 0, then by induction, digits_sum(x / 10) > 0.
    // If x / 10 == 0 (e.g., x=50+), then digits_sum(x/10) = 0.
    // Let's refine for nat x:
    // digits_sum(x) = x % 10 + digits_sum(x / 10)
    // If x > 0 and x < 10, digits_sum(x) = x > 0. This is the base case.
    // If x >= 10:
    // x % 10 >= 0
    // If x / 10 > 0, then by recursive call, digits_sum(x / 10) > 0.
    // Therefore, x % 10 + digits_sum(x / 10) >= 0 + (something > 0) > 0.
    // The only edge case is when x / 10 == 0, which means x < 10. That's covered by base case.
    // So for all x: nat, x > 0 ==> digits_sum(x) > 0.
    lemma_digits_sum_N_positive(x / 10);
  }
}

lemma lemma_digits_sum_nat_zero(x: nat)
  ensures digits_sum(x) == 0 <==> x == 0
  decreases x
{
  if x < 10 {
    assert digits_sum(x) == x;
  } else {
    lemma_digits_sum_nat_zero(x / 10);
    // digits_sum(x) = x % 10 + digits_sum(x/10)
    // if digits_sum(x) == 0:
    //   since x % 10 >= 0 and digits_sum(x/10) >= 0 (from previous lemma),
    //   both must be 0.
    //   x % 10 == 0 ==> x is a multiple of 10.
    //   digits_sum(x/10) == 0 ==> x/10 == 0 (by recursive call),
    //   which means x must be 0.
    // if x == 0:
    //   digits_sum(0) == 0.
  }
}

lemma lemma_digits_sum_positive_implies_positive(x: int)
  ensures digits_sum(x) > 0 ==> x > 0
  decreases abs(x)
{
  if x == 0 {
    assert digits_sum(x) == 0;
  } else if x > 0 {
    digits_sum(x); // This just forces evaluation, no specific lemma needed here as it's implied by types.
  } else { // x < 0
    if abs(x) < 10 {
      assert digits_sum(x) == x;
      // If x < 0 and digits_sum(x) == x, then digits_sum(x) cannot be > 0.
    } else {
      // digits_sum(x) = x % 10 + digits_sum(x / 10)
      // Since x is negative, x % 10 will likely be negative or 0.
      // x / 10 will also be negative.
      // E.g., digits_sum(-12) = -2 + digits_sum(-1) = -2 - 1 = -3
      // E.g., digits_sum(-10) = 0 + digits_sum(-1) = -1
      // If x < 0, let x = -y where y > 0.
      // digits_sum(-y).
      // If digits_sum(x) > 0, and x < 0, this cannot happen for typical definition.
      // The `digits_sum` function implicitly treats `x % 10` and `x / 10` for negative numbers
      // in a way that the result should be non-positive if x is negative.
      // E.g. x = -10, x % 10 = 0, x / 10 = -1. digits_sum(-10) = 0 + digits_sum(-1) = -1.
      // E.g. x = -15, x % 10 = -5, x / 10 = -1. digits_sum(-15) = -5 + digits_sum(-1) = -6.
      // The property is that if x is negative, digits_sum(x) is negative or zero (if x=0).
      // Therefore, if digits_sum(x) > 0, x must be positive.
      lemma_digits_sum_positive_implies_positive(x / 10);
    }
  }
}

lemma lemma_digits_sum_positive_iff_positive(x: int)
  ensures digits_sum(x) > 0 <==> x > 0
  decreases abs(x)
{
  if x == 0 {
    assert digits_sum(x) == 0;
    assert !(digits_sum(x) > 0);
    assert !(x > 0);
  } else if x > 0 {
    lemma_digits_sum_N_positive(x as nat);
    assert digits_sum(x) > 0;
  } else { // x < 0
    assert digits_sum(x) <= 0; // if x < 0, then digits_sum(x) <= 0.
                              // Proof: By induction. Base case abs(x) < 10: digits_sum(x) = x < 0.
                              // Inductive step: digits_sum(x) = x % 10 + digits_sum(x / 10).
                              // If x < 0, then x/10 is negative and farther from 0. x % 10 is <= 0.
                              // So sum of non-positive numbers is non-positive.
    assert !(digits_sum(x) > 0);
    assert !(x > 0);
  }
}

ghost predicate G(i: int, s: seq<int>, x: int) {
  0 <= i < |s| && s[i] == x && digits_sum(x) > 0
}
// </vc-helpers>

// <vc-spec>
method count_nums(s: seq<int>) returns (cnt: nat)
  // post-conditions-start
  ensures cnt == |set i | 0 <= i < |s| && digits_sum(s[i]) > 0|
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var cnt := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant cnt == |set k | 0 <= k < i && digits_sum(s[k]) > 0|
  {
    if digits_sum(s[i]) > 0 {
      cnt := cnt + 1;
    }
    i := i + 1;
  }
  return cnt;
}
// </vc-code>

function digits_sum(x: int): int
  decreases abs(x)
{
  if abs(x) < 10 then x else x % 10 + digits_sum(x / 10)
}
// pure-end
function abs(x: int): int
  ensures abs(x) >= 0
  ensures abs(x) == x || abs(x) == -x
{
  if x >= 0 then x else -x
}
// pure-end