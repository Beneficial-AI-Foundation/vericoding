predicate ValidInput(n: int, a_1: seq<int>, a_2: seq<int>)
{
    n >= 1 &&
    |a_1| == n && |a_2| == n &&
    forall i :: 0 <= i < n ==> 1 <= a_1[i] <= 100 && 1 <= a_2[i] <= 100
}

function sum_range(s: seq<int>, start: int, end: int): int
    requires 0 <= start <= end <= |s|
    requires forall i :: start <= i < end ==> s[i] >= 1
    decreases end - start
    ensures sum_range(s, start, end) >= 0
    ensures start < end ==> sum_range(s, start, end) >= end - start
    ensures start < end && (forall i :: start <= i < end ==> s[i] <= 100) ==> sum_range(s, start, end) <= (end - start) * 100
{
    if start == end then 0
    else s[start] + sum_range(s, start + 1, end)
}

predicate IsValidResult(n: int, a_1: seq<int>, a_2: seq<int>, result: int)
    requires ValidInput(n, a_1, a_2)
{
    result >= n + 1 &&
    result <= (n + 1) * 100 &&
    exists i :: 0 <= i < n && result == sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n) &&
    forall i :: 0 <= i < n ==> result >= sum_range(a_1, 0, i + 1) + sum_range(a_2, i, n)
}

// <vc-helpers>
lemma SumRangeCons(s: seq<int>, start: int, end: int)
    requires 0 <= start < end <= |s|
    requires forall i :: start <= i < end ==> s[i] >= 1
    ensures sum_range(s, start, end) == s[start] + sum_range(s, start + 1, end)
{
    // Follows from the definition of sum_range
    assert sum_range(s, start, end) == s[start] + sum_range(s, start + 1, end);
}

lemma SumRangeAppend(s: seq<int>, start: int, mid: int, end: int)
    requires 0 <= start <= mid <= end <= |s|
    requires forall i :: start <= i < end ==> s[i] >= 1
    ensures sum_range(s, start, end) == sum_range(s, start, mid) + sum_range(s, mid, end)
    decreases end - start
{
    if start == end {
        // all ranges empty
        assert sum_range(s, start, end) == 0;
        assert sum_range(s, start, mid) == 0;
        assert sum_range(s, mid, end) == 0;
    } else {
        if start < mid {
            // unfold head
            assert sum_range(s, start, end) == s[start] + sum_range(s, start + 1, end);
            assert sum_range(s, start, mid) == s[start] + sum_range(s, start + 1, mid);
            SumRangeAppend(s, start + 1, mid, end);
            assert sum_range(s, start + 1, end) == sum_range(s, start + 1, mid) + sum_range(s, mid, end);
            assert sum_range(s, start, end) == s[start] + (sum_range(s, start + 1, mid) + sum_range(s, mid, end));
            assert s[start] + sum_range(s, start + 1, mid) == sum_range(s, start, mid);
            assert sum_range(s, start, end) == sum_range(s, start, mid) + sum_range(s, mid, end);
        } else {
            // start == mid
            assert mid == start;
            assert sum_range(s, start, mid) == 0;
            assert sum_range(s, mid, end) == sum_range(s, start, end);
            assert sum_range(s, start, mid) + sum_range(s, mid, end) == sum_range(s, start, end);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a_1: seq<int>, a_2: seq<int>) returns (result: int)
    requires ValidInput(n, a_1, a_2)
    ensures IsValidResult(n, a_1, a_2, result)
// </vc-spec>
// <vc-code>
{
  // Initialize for i = 0
  var i := 0;
  var sumA1 := a_1[0]; // sum_range(a_1, 0, 1)
  // make the connection explicit for the invariant
  SumRangeCons(a_1, 0, 1);
  assert sumA1 == sum_range(a_1, 0, 1);

  var sumA2 := sum_range(a_2, 0, n);
  var best := sumA1 + sumA2;
  // Loop to consider splits i = 0 .. n-1, maintaining best as max over processed i's
  while i < n - 1
    invariant 0 <= i < n
    invariant sumA1 == sum_range(a_1, 0, i + 1)
    invariant sumA2 == sum_range(a_2, i, n)
    invariant forall j :: 0 <= j <= i ==> best >= sum_range(a_1, 0, j + 1) + sum_range(a_2, j, n)
    invariant exists k :: 0 <= k <= i && best == sum_range(a_1, 0, k + 1) + sum_range(a_2, k, n)
    decreases n - 1 - i
  {
    // Decompose sumA2 = sum_range(a_2, i, n) into a_2[i] + sum_range(a_2, i+1, n)
    SumRangeCons(a_2, i, n);
    var nextSumA2 := sumA2 - a_2[i]; // equals sum_range(a_2, i+1, n)
    var oldi := i;
    var oldsumA1 := sumA1;
    i := i + 1;
    sumA2 := nextSumA2;
    // establish sumA2 == sum_range(a_2, i, n) for new i
    assert sumA2 == sum_range(a_2, i, n);

    // Update sumA1: oldsumA1 + a_1[i] should equal sum_range(a_1, 0, i+1)
    // Use split lemma: sum_range(0, i+1) == sum_range(0, oldi+1) + sum_range(oldi+1, i+1)
    SumRangeAppend(a_1, 0, oldi + 1, i + 1);
    // And the small range equals the single element
    SumRangeCons(a_1, oldi + 1, i + 1);
    sumA1 := oldsumA1 + a_1[i];
    assert sumA1 == sum_range(a_1, 0, i + 1);

    var candidate := sumA1 + sumA2;
    if candidate > best {
      best := candidate;
    } else {
      // make explicit that best >= candidate to help the verifier
      assert best >= candidate;
    }
  }
  result := best;
}
// </vc-code>

