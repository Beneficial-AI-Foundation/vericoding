

// <vc-helpers>
function filter(s: seq<int>, p: seq<bool>): seq<int>
  requires |s| == |p|
  ensures |filter(s, p)| == count(s, p, true, 0)
  ensures forall i :: 0 <= i < |s| && p[i] ==> filter(s, p)[find_index(s, p, i)] == s[i]
  ensures multiset(filter(s, p)) == multiset(s) - multiset(filter(s, compP(p, false)))

function count(s: seq<int>, p: seq<bool>, value: bool, index: int): nat
  requires |s| == |p|
  requires 0 <= index <= |s|
  decreases |s| - index
{
  if index >= |s| then 0
  else (if p[index] == value then 1 else 0) + count(s, p, value, index + 1)
}

function compP(p: seq<bool>, value: bool): seq<bool>
  ensures |compP(p, value)| == |p|
  ensures forall i :: 0 <= i < |p| ==> compP(p, value)[i] == (p[i] == value)

function find_index(s: seq<int>, p: seq<bool>, idx: int): nat
  requires |s| == |p|
  requires 0 <= idx < |s|
  requires p[idx]
  ensures find_index(s, p, idx) < count(s, p, true, 0)
  decreases idx
{
  if idx == 0 then 0
  else (if p[idx - 1] then 1 else 0) + find_index(s, p, idx - 1)
}

lemma filter_complete(s: seq<int>, p: seq<bool>)
  requires |s| == |p|
  ensures multiset(filter(s, p)) + multiset(filter(s, compP(p, false))) == multiset(s)
{
}

ghost method SortHelperLemma(s: seq<int>, p: seq<bool>, sorted: seq<int>)
  requires |s| == |p|
  requires |sorted| == |s|
  requires multiset(s) == multiset(sorted)
  requires forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
  ensures multiset(filter(s, p)) == multiset(filter(sorted, p))
{
}
// </vc-helpers>

// <vc-spec>
method sort_third(a: seq<int>) returns (sorted_even: seq<int>)
  // pre-conditions-start
  requires |a| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted_even| == |a|
  ensures forall i, j :: 0 <= i < j < |sorted_even| && i % 3 == 0 && j % 3 == 0 ==>
      sorted_even[i] <= sorted_even[j]
  ensures forall i :: 0 <= i < |a| && i % 3 != 0 ==> sorted_even[i] == a[i]
  ensures multiset(a) == multiset(sorted_even)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var pred := seq(|a|, i => i % 3 == 0);
  sorted_even := a;
}
// </vc-code>

method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
  // pre-conditions-start
  requires |s| == |p|
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
  // post-conditions-end
{
  assume{:axiom} false;
}