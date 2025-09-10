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
lemma SumNonNegative(s: seq<int>)
  requires forall i :: 0 <= i < |s| ==> s[i] >= 0
  ensures sum(s) >= 0
{
  if |s| == 0 {
  } else {
    SumNonNegative(s[1..]);
  }
}

lemma SumSlice(s: seq<int>, start: int, end: int)
  requires 0 <= start <= end <= |s|
  ensures sum(s[start..end]) == (if start == end then 0 else s[start] + sum(s[start+1..end]))
{
}

lemma SumCons(x: int, s: seq<int>)
  ensures sum([x] + s) == x + sum(s)
{
}

lemma SumConcat(s1: seq<int>, s2: seq<int>)
  ensures sum(s1 + s2) == sum(s1) + sum(s2)
{
  if |s1| == 0 {
  } else {
    SumConcat(s1[1..], s2);
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
  var schedule := a;
  additionalWalks := 0;
  
  var i := 0;
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant |schedule| == n
    invariant forall j :: 0 <= j < n ==> schedule[j] >= a[j]
    invariant additionalWalks == sum(schedule) - sum(a)
    invariant additionalWalks >= 0
    invariant forall j :: 0 <= j < i ==> j < n - 1 ==> schedule[j] + schedule[j + 1] >= k
  {
    if schedule[i] + schedule[i + 1] < k {
      var needed := k - (schedule[i] + schedule[i + 1]);
      schedule := schedule[0..i + 1] + [schedule[i + 1] + needed] + schedule[i + 2..];
      additionalWalks := additionalWalks + needed;
    }
    i := i + 1;
  }
  
  finalSchedule := schedule;
}
// </vc-code>

