function sum(s: seq<int>): int
{
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}

predicate ValidInput(n: int, k: int, a: seq<int>)
{
    n >= 1 && |a| == n && k >= 0 && forall i :: 0 <= i < n ==> a[i] >= 0
}

predicate ValidOutput(a: seq<int>, finalSchedule: seq<int>, additionalWalks: int, k: int)
{
    |finalSchedule| == |a| &&
    additionalWalks >= 0 &&
    forall i :: 0 <= i < |a| ==> finalSchedule[i] >= a[i] &&
    forall i :: 0 <= i < |a| - 1 ==> finalSchedule[i] + finalSchedule[i + 1] >= k &&
    additionalWalks == sum(finalSchedule) - sum(a)
}

// <vc-helpers>
lemma SumMonotonic(s: seq<int>, t: seq<int>)
  requires |s| == |t|
  requires forall i :: 0 <= i < |s| ==> s[i] <= t[i]
  ensures sum(s) <= sum(t)
  decreases |s|
{
  if |s| == 0 {
  } else {
    assert s[0] <= t[0];
    assert |s[1..]| == |t[1..]|;
    assert forall i :: 0 <= i < |s[1..]| ==> s[1..][i] <= t[1..][i] by {
      assert 0 <= i + 1 < |s|;
    }
    SumMonotonic(s[1..], t[1..]);
    assert sum(s) == s[0] + sum(s[1..]);
    assert sum(t) == t[0] + sum(t[1..]);
    assert s[0] + sum(s[1..]) <= t[0] + sum(t[1..]);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, a: seq<int>) returns (additionalWalks: int, finalSchedule: seq<int>)
    requires ValidInput(n, k, a)
    ensures ValidOutput(a, finalSchedule, additionalWalks, k)
// </vc-spec>
// <vc-code>
{
  assert |a| == n;
  finalSchedule := seq i | 0 <= i < n :: if a[i] < k then k else a[i];

  // Element-wise dominance to aid proofs
  assert forall i :: 0 <= i < |a| ==> finalSchedule[i] >= a[i] by {
    if a[i] < k {
      assert finalSchedule[i] == k;
      assert k >= a[i];
    } else {
      assert a[i] >= k;
      assert finalSchedule[i] == a[i];
    }
  }

  // Neighbor sum property
  assert forall i :: 0 <= i < |a| - 1 ==> finalSchedule[i] + finalSchedule[i + 1] >= k by {
    // Each entry is at least k
    if a[i] < k {
      assert finalSchedule[i] == k;
    } else {
      assert finalSchedule[i] == a[i];
      assert finalSchedule[i] >= k;
    }
    if a[i + 1] < k {
      assert finalSchedule[i + 1] == k;
    }
// </vc-code>

