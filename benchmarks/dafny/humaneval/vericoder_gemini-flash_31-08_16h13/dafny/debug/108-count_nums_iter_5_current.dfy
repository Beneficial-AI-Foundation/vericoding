

// <vc-helpers>
lemma lemma_digits_sum_nonNegative(x: int)
  ensures digits_sum(x) <= 0 ==> x == 0
  decreases abs(x)
{
  if abs(x) < 10 {
  } else {
    lemma_digits_sum_nonNegative(x / 10);
  }
}

lemma lemma_digits_sum_N_positive(x: nat)
  ensures x > 0 ==> digits_sum(x) > 0
  decreases x
{
  if x < 10 {
  } else {
    lemma_digits_sum_N_positive(x / 10);
  }
}

lemma lemma_digits_sum_nat_zero(x: nat)
  ensures digits_sum(x) == 0 <==> x == 0
  decreases x
{
  if x < 10 {
  } else {
    lemma_digits_sum_nat_zero(x / 10);
  }
}

lemma lemma_digits_sum_positive_implies_positive(x: int)
  ensures digits_sum(x) > 0 ==> x > 0
  decreases abs(x)
{
  if x == 0 {
  } else if x > 0 {
    lemma_digits_sum_N_positive(x as nat);
  } else { // x < 0
    if abs(x) < 10 {
    } else {
      assert x < 0;
      assert x/10 < 0;
      lemma_digits_sum_positive_implies_positive(x / 10);
      assert (x % 10 <= 0); // x % 10 can be negative or zero for negative x
      assert (digits_sum(x/10) <= 0); // by inductive hypothesis on x/10, if digits_sum(x/10) > 0, then x/10 > 0, which contradicts x/10 < 0
      assert digits_sum(x) == x % 10 + digits_sum(x / 10);
      assert digits_sum(x) <= 0; // sum of two non-positive numbers is non-positive
    }
  }
}

lemma lemma_digits_sum_positive_iff_positive(x: int)
  ensures digits_sum(x) > 0 <==> x > 0
  decreases abs(x)
{
  if x == 0 {
  } else if x > 0 {
    lemma_digits_sum_N_positive(x as nat);
  } else { // x < 0
    lemma_digits_sum_positive_implies_positive(x); // This proves digits_sum(x) > 0 ==> x > 0.
                                                  // Since x < 0, it means digits_sum(x) is not > 0.
                                                  // So, if x < 0, then digits_sum(x) <= 0.
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
  var current_cnt := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant current_cnt == |set k | 0 <= k < i && digits_sum(s[k]) > 0|
  {
    lemma_digits_sum_positive_iff_positive(s[i]); // Add this lemma call
    if digits_sum(s[i]) > 0 {
      current_cnt := current_cnt + 1;
    }
    i := i + 1;
  }
  return current_cnt;
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