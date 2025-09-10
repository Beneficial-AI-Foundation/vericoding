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
    assert s1 + s2 == s2;
  } else if |s2| == 0 {
    assert s1 + s2 == s1;
  } else {
    calc {
      sum(s1 + s2);
      == { assert (s1 + s2)[0] == s1[0]; }
      s1[0] + sum((s1 + s2)[1..]);
      == { assert (s1 + s2)[1..] == s1[1..] + s2; }
      s1[0] + sum(s1[1..] + s2);
      == { SumConcat(s1[1..], s2); }
      s1[0] + (sum(s1[1..]) + sum(s2));
      == { assert sum(s1) == s1[0] + sum(s1[1..]); }
      sum(s1) + sum(s2);
    }
  }
}

lemma SumAppendSingle(s: seq<int>, x: int)
  ensures sum(s + [x]) == sum(s) + x
{
  if |s| == 0 {
    assert sum([x]) == x;
  } else {
    calc {
      sum(s + [x]);
      == { SumConcat(s, [x]); }
      sum(s) + sum([x]);
      == { assert sum([x]) == x; }
      sum(s) + x;
    }
  }
}

lemma SumRangeSplit(s: seq<int>, i: int)
  requires 0 <= i <= |s|
  ensures sum(s[0..i] + s[i..]) == sum(s)
{
  assert s[0..i] + s[i..] == s;
}

lemma SumSequenceUpdate(s: seq<int>, i: int, value: int)
  requires 0 <= i < |s|
  ensures sum(s[i := value]) == sum(s) - s[i] + value
{
  calc {
    sum(s[i := value]);
    == { SumConcat(s[0..i], [value] + s[i+1..]); }
    sum(s[0..i]) + sum([value] + s[i+1..]);
    == { SumCons(value, s[i+1..]); }
    sum(s[0..i]) + value + sum(s[i+1..]);
    == // Original sum: sum(s[0..i]) + s[i] + sum(s[i+1..])
    sum(s) - s[i] + value;
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
    invariant forall j :: 0 <= j < i ==> schedule[j] + schedule[j + 1] >= k
  {
    if schedule[i] + schedule[i + 1] < k {
      var needed := k - (schedule[i] + schedule[i + 1]);
      
      // Update the i+1 element
      var updated_value := schedule[i + 1] + needed;
      schedule := schedule[0..i + 1] + [updated_value] + schedule[i + 2..];
      
      // Update additionalWalks
      additionalWalks := additionalWalks + needed;
      
      // Verify sum invariant using the lemma
      assert sum(schedule) == sum(schedule[0..i + 1] + [updated_value] + schedule[i + 2..]);
      assert sum(schedule) == sum(schedule[0..i + 1]) + updated_value + sum(schedule[i + 2..]);
      assert sum(schedule) == (sum(schedule[0..i]) + schedule[i]) + (schedule[i + 1] + needed) + sum(schedule[i + 2..]);
      assert sum(schedule) == sum(schedule[0..i]) + schedule[i] + schedule[i + 1] + needed + sum(schedule[i + 2..]);
      assert sum(schedule) == sum(schedule[0..i]) + schedule[i] + schedule[i + 1] + sum(schedule[i + 2..]) + needed;
    }
    i := i + 1;
  }
  
  finalSchedule := schedule;
}
// </vc-code>

