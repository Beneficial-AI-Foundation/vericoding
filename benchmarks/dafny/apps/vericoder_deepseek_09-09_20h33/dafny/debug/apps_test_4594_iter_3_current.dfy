predicate ValidInput(diameters: seq<int>)
{
    |diameters| > 0 && forall i :: 0 <= i < |diameters| ==> diameters[i] > 0
}

function num_distinct(s: seq<int>): int
    ensures num_distinct(s) >= 0
    ensures num_distinct(s) <= |s|
    ensures |s| == 0 ==> num_distinct(s) == 0
    ensures |s| > 0 ==> num_distinct(s) >= 1
{
    if |s| == 0 then 0
    else if s[0] in s[1..] then num_distinct(s[1..])
    else 1 + num_distinct(s[1..])
}

// <vc-helpers>
lemma CountDistinctLemma(s: seq<int>, start: int, end: int, seen: set<int>, count: int)
  requires 0 <= start <= end <= |s|
  requires count == |seen|
  requires forall i :: 0 <= i < end ==> (i < start ==> s[i] in seen) && (i >= start ==> s[i] !in seen)
  ensures num_distinct(s) == count + num_distinct(s[start..end])
  decreases end - start
{
  if start == end {
    assert s[start..end] == [];
    assert num_distinct(s[start..end]) == 0;
  } else {
    var first := s[start];
    if first in s[start+1..end] {
      assert first in seen; // From precondition: s[i] !in seen for i >= start, but first is at start
      CountDistinctLemma(s, start+1, end, seen, count);
      assert num_distinct(s[start..end]) == num_distinct(s[start+1..end]);
    } else {
      CountDistinctLemma(s, start+1, end, seen, count);
      assert num_distinct(s[start..end]) == 1 + num_distinct(s[start+1..end]);
    }
  }
}

lemma LoopInvariantHelper(s: seq<int>, i: int, seen: set<int>, count: int)
  requires 0 <= i <= |s|
  requires count == |seen|
  requires forall j :: 0 <= j < i ==> s[j] in seen
  requires forall x :: x in seen ==> exists j :: 0 <= j < i && s[j] == x
  ensures forall k :: 0 <= k < |s| ==> (k < i ==> s[k] in seen) && (k >= i ==> s[k] !in seen)
{
}
// </vc-helpers>

// <vc-spec>
method solve(diameters: seq<int>) returns (result: int)
    requires ValidInput(diameters)
    ensures result == num_distinct(diameters)
    ensures result >= 1
    ensures result <= |diameters|
// </vc-spec>
// <vc-code>
{
  var n := |diameters|;
  var distinctCount := 0;
  var seen: set<int> := {};
  
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant distinctCount == |seen|
    invariant forall x :: x in seen ==> exists j :: 0 <= j < i && diameters[j] == x
    invariant forall j :: 0 <= j < i ==> diameters[j] in seen
    invariant num_distinct(diameters) == distinctCount + num_distinct(diameters[i..])
    decreases n - i
  {
    // Update the seen set and count
    if diameters[i] !in seen {
      distinctCount := distinctCount + 1;
      seen := seen + {diameters[i]};
    }
    
    // Prove the precondition needed for CountDistinctLemma
    LoopInvariantHelper(diameters, i, seen, distinctCount);
    CountDistinctLemma(diameters, i, n, seen, distinctCount);
    i := i + 1;
  }
  assert i == n;
  assert diameters[n..] == [];
  assert num_distinct(diameters[n..]) == 0;
  result := distinctCount;
}
// </vc-code>

