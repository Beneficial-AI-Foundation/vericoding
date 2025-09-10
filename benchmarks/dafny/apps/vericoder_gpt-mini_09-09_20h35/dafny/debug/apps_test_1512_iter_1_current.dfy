predicate ValidPermutation(p: seq<int>, n: int)
{
  |p| == n && n >= 1 &&
  (forall i :: 0 <= i < n ==> 1 <= p[i] <= n) &&
  (forall i, j :: 0 <= i < j < n ==> p[i] != p[j])
}

function countRecords(s: seq<int>): int
  ensures countRecords(s) >= 0
{
  if |s| == 0 then 0
  else 1 + countRecordsFromIndex(s, 1, s[0])
}

function countRecordsAfterRemoval(p: seq<int>, toRemove: int): int
  requires forall i :: 0 <= i < |p| ==> 1 <= p[i] <= |p|
  requires forall i, j :: 0 <= i < j < |p| ==> p[i] != p[j]
  requires toRemove in p
{
  var filtered := seq(|p| - 1, i requires 0 <= i < |p| - 1 => 
    if indexOf(p, toRemove) <= i then p[i + 1] else p[i]);
  countRecords(filtered)
}

// <vc-helpers>
// No helpers needed for this proof.
// </vc-helpers>

// <vc-spec>
method solve(n: int, p: seq<int>) returns (result: int)
  requires ValidPermutation(p, n)
  ensures 1 <= result <= n
  ensures result in p
  ensures forall x :: x in p ==> countRecordsAfterRemoval(p, result) >= countRecordsAfterRemoval(p, x)
  ensures forall x :: x in p && countRecordsAfterRemoval(p, x) == countRecordsAfterRemoval(p, result) ==> result <= x
// </vc-spec>
// <vc-code>
{
  var best := p[0];
  var bestVal := countRecordsAfterRemoval(p, best);
  var i := 1;
  while i < n
    invariant 0 <= i <= n
    invariant exists k :: 0 <= k < i && best == p[k]
    invariant bestVal == countRecordsAfterRemoval(p, best)
    invariant forall j :: 0 <= j < i ==>
      countRecordsAfterRemoval(p, best) > countRecordsAfterRemoval(p, p[j]) ||
      (countRecordsAfterRemoval(p, best) == countRecordsAfterRemoval(p, p[j]) && best <= p[j])
  {
    var v := countRecordsAfterRemoval(p, p[i]);
    if v > bestVal || (v == bestVal && p[i] < best) {
      best := p[i];
      bestVal := v;
    }
    i := i + 1;
  }
  result := best;
}
// </vc-code>

