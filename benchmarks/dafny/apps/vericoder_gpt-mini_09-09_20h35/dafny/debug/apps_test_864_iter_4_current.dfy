function possible(n: int, foodTypes: seq<int>, days: int): bool
    requires n >= 0
    requires days >= 0
    requires forall i :: 0 <= i < |foodTypes| ==> foodTypes[i] >= 1
{
    if days == 0 then true
    else
        var totalParticipants := countTotalParticipants(foodTypes, days, 1);
        totalParticipants >= n
}

function countTotalParticipants(foodTypes: seq<int>, days: int, currentType: int): int
    requires days >= 0
    requires currentType >= 1
    decreases 101 - currentType
    ensures countTotalParticipants(foodTypes, days, currentType) >= 0
    ensures days > 0 ==> countTotalParticipants(foodTypes, days + 1, currentType) <= countTotalParticipants(foodTypes, days, currentType)
{
    if currentType > 100 then 0
    else
        var packagesOfThisType := countPackages(foodTypes, currentType);
        var participantsForThisType := if days > 0 then packagesOfThisType / days else 0;
        participantsForThisType + countTotalParticipants(foodTypes, days, currentType + 1)
}

function countPackages(foodTypes: seq<int>, targetType: int): int
    requires targetType >= 1
    ensures countPackages(foodTypes, targetType) >= 0
    ensures countPackages(foodTypes, targetType) <= |foodTypes|
{
    if |foodTypes| == 0 then 0
    else if foodTypes[0] == targetType then 1 + countPackages(foodTypes[1..], targetType)
    else countPackages(foodTypes[1..], targetType)
}

// <vc-helpers>
method Lemma_countTotal_zero_if_days_gt_len(foodTypes: seq<int>, days: int, currentType: int)
    requires days > |foodTypes|
    requires currentType >= 1
    decreases 101 - currentType
    ensures countTotalParticipants(foodTypes, days, currentType) == 0
{
    if currentType > 100 {
        // by definition countTotalParticipants(...) == 0
    } else {
        var packages := countPackages(foodTypes, currentType);
        assert packages >= 0;
        assert packages <= |foodTypes|;
        assert |foodTypes| < days;
        assert packages < days;
        assert packages / days == 0;
        Lemma_countTotal_zero_if_days_gt_len(foodTypes, days, currentType + 1);
        // Unfolding the function gives the result.
    }
}

method Lemma_monotone_days(foodTypes: seq<int>, a: int, b: int, currentType: int)
    requires 0 < a <= b
    requires currentType >= 1
    decreases b - a
    ensures countTotalParticipants(foodTypes, b, currentType) <= countTotalParticipants(foodTypes, a, currentType)
{
    if a == b {
        // trivial
    } else {
        Lemma_monotone_days(foodTypes, a, b - 1, currentType);
        if b - 1 > 0 {
            assert countTotalParticipants(foodTypes, b, currentType) <= countTotalParticipants(foodTypes, b - 1, currentType);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, foodTypes: seq<int>) returns (result: int)
    requires 1 <= n <= 100
    requires 1 <= m <= 100
    requires |foodTypes| == m
    requires forall i :: 0 <= i < |foodTypes| ==> 1 <= foodTypes[i] <= 100
    ensures result >= 0
    ensures result <= m
    ensures result > 0 ==> possible(n, foodTypes, result)
    ensures !possible(n, foodTypes, result + 1)
    ensures forall d :: d > result ==> !possible(n, foodTypes, d)
// </vc-spec>
// <vc-code>
{
  var result := 0;
  var i := 1;
  // invariants to help verification
  while i <= m
    invariant 0 <= result <= m
    invariant 1 <= i <= m + 1
    invariant forall k :: 1 <= k < i ==> (possible(n, foodTypes, k) ==> k <= result)
    invariant result > 0 ==> possible(n, foodTypes, result)
  {
    if possible(n, foodTypes, i) {
      result := i;
    }
    i := i + 1;
  }

  // After the loop, i == m + 1
  assert i == m + 1;

  // Prove !possible(n, foodTypes, result + 1)
  if result + 1 <= m {
    var k := result + 1;
    assert 1 <= k;
    assert k < i;
    if possible(n, foodTypes, k) {
      // From invariant with i = m+1 we have for all 1 <= t < i: possible(t) ==> t <= result
      assert (forall t :: 1 <= t < i ==> (possible(n, foodTypes, t) ==> t <= result));
      assert possible(n, foodTypes, k) ==> k <= result;
      assert k <= result;
      assert k > result; // contradiction, so possible(k) cannot hold
    }
  } else {
    // result + 1 > m  => result+1 > |foodTypes|, so countTotalParticipants == 0
    Lemma_countTotal_zero_if_days_gt_len(foodTypes, result + 1, 1);
    assert countTotalParticipants(foodTypes, result + 1, 1) == 0;
    assert !(countTotalParticipants(foodTypes, result + 1, 1) >= n);
  }

  // Prove forall d :: d > result ==> !possible(n, foodTypes, d)
  var d := result + 1;
  while d <= m
    invariant result + 1 <= d <= m + 1
    decreases m - d + 1
  {
    if possible(n, foodTypes, d) {
      // Use the invariant established by the previous loop: i == m+1 and
      // forall k :: 1 <= k < i ==> (possible(k) ==> k <= result)
      assert i == m + 1;
      assert 1 <= d;
      assert d < i;
      assert possible(n, foodTypes, d) ==> d <= result;
      assert d <= result;
      assert d > result; // contradiction
    }
    d := d + 1;
  }

  // For all d > m, total participants are zero, hence not possible.
  assert forall dd | dd > m :: countTotalParticipants(foodTypes, dd, 1) == 0
    by {
      Lemma_countTotal_zero_if_days_gt_len(foodTypes, dd, 1);
      assert countTotalParticipants(foodTypes, dd, 1) == 0;
    }

  // Combine the two cases into the required forall
  assert forall D | D > result ::
    if D <= m then !possible(n, foodTypes, D) else !(countTotalParticipants(foodTypes, D, 1) >= n)
    by {
      assert i == m + 1;
      if D <= m {
        // D was handled in the finite loop above
        assert 1 <= D;
        assert D < i;
        assert possible(n, foodTypes, D) ==> D <= result;
        assert D > result;
        assert !possible(n, foodTypes, D);
      } else {
        // D > m
        Lemma_countTotal_zero_if_days_gt_len(foodTypes, D, 1);
        assert countTotalParticipants(foodTypes, D, 1) == 0;
        assert !(countTotalParticipants(foodTypes, D, 1) >= n);
      }
    }

  result
}
// </vc-code>

