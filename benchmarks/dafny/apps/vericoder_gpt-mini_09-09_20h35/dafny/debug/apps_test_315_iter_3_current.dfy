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
predicate ValidOutput(a: seq<int>, finalSchedule: seq<int>, additionalWalks: int, k: int)
{
    |finalSchedule| == |a| &&
    additionalWalks >= 0 &&
    (forall i {:trigger finalSchedule[i], a[i]} :: 0 <= i < |a| ==> finalSchedule[i] >= a[i]) &&
    (forall i {:trigger finalSchedule[i], finalSchedule[i+1]} :: 0 <= i < |a| - 1 ==> finalSchedule[i] + finalSchedule[i + 1] >= k) &&
    additionalWalks == sum(finalSchedule) - sum(a)
}

lemma Sum_monotone_ge(s: seq<int>, t: seq<int>)
  requires |s| == |t|
  requires forall i {:trigger s[i], t[i]} :: 0 <= i < |s| ==> s[i] >= t[i]
  ensures sum(s) >= sum(t)
  decreases |s|
{
  if |s| == 0 {
    // trivial
  } else {
    assert sum(s) == s[0] + sum(s[1..]);
    assert sum(t) == t[0] + sum(t[1..]);
    assert s[0] >= t[0];
    Sum_monotone_ge(s[1..], t[1..]);
    assert sum(s[1..]) >= sum(t[1..]);
    // Combine the inequalities
    assert sum(s) >= sum(t);
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
  var b := new int[n];
  // finalSchedule will be b[..] at the end
  b[0] := a[0];
  var processed := 1;
  while processed < n
    invariant 1 <= processed <= n
    invariant forall t {:trigger b[t], a[t]} :: 0 <= t < processed ==> b[t] >= a[t]
    invariant forall t {:trigger b[t], b[t+1]} :: 0 <= t < processed - 1 ==> b[t] + b[t+1] >= k
    decreases n - processed
  {
    var need := k - b[processed - 1];
    if need < a[processed] {
      b[processed] := a[processed];
    } else {
      b[processed] := need;
    }
    processed := processed + 1;
  }

  finalSchedule := b[..];
  additionalWalks := sum(finalSchedule) - sum(a);
  // prove non-negativity of additionalWalks
  Sum_monotone_ge(finalSchedule, a);
  assert additionalWalks >= 0;
}
// </vc-code>

