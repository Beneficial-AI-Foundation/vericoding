predicate ValidInput(n: int, v: int, sellers: seq<seq<int>>) {
    n >= 0 && v >= 0 && |sellers| == n && 
    forall i :: 0 <= i < |sellers| ==> |sellers[i]| > 0
}

predicate ValidOutput(count: int, indices: seq<int>, n: int) {
    count == |indices| && count >= 0 && count <= n &&
    (forall i :: 0 <= i < |indices| ==> 1 <= indices[i] <= n) &&
    (forall i :: 0 <= i < |indices| - 1 ==> indices[i] < indices[i+1])
}

predicate CorrectSolution(v: int, sellers: seq<seq<int>>, indices: seq<int>) 
    requires forall i :: 0 <= i < |sellers| ==> |sellers[i]| > 0
    requires forall i :: 0 <= i < |indices| ==> 1 <= indices[i] <= |sellers|
{
    (forall i :: 0 <= i < |indices| ==> v > Min(sellers[indices[i] - 1])) &&
    (forall i :: 0 <= i < |sellers| ==> (v > Min(sellers[i]) <==> (i + 1) in indices))
}

// <vc-helpers>
function Min(s: seq<int>): int
  requires |s| > 0
{
  if |s| == 1 then s[0]
  else
    var m := Min(s[1..]);
    if s[0] < m then s[0] else m
}

lemma MinLemma(s: seq<int>, i: int)
  requires |s| > 0
  requires 0 <= i < |s|
  ensures Min(s) <= s[i]

lemma MinInSequence(s: seq<int>)
  requires |s| > 0
  ensures exists i :: 0 <= i < |s| && s[i] == Min(s)

lemma MinSubsequence(s: seq<int>, start: int, end: int)
  requires |s| > 0
  requires 0 <= start <= end < |s|
  ensures Min(s[start..end+1]) >= Min(s)

lemma MinCons(s: seq<int>, x: int)
  requires |s| > 0
  ensures Min([x] + s) == (if x < Min(s) then x else Min(s))

lemma SequenceContainsOwnElements(s: seq<int>, x: int)
  ensures x in s ==> exists i :: 0 <= i < |s| && s[i] == x
{
}

lemma SortedSequenceIndices(s: seq<int>)
  requires forall i :: 0 <= i < |s| - 1 ==> s[i] < s[i+1]
  ensures forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, v: int, sellers: seq<seq<int>>) returns (count: int, indices: seq<int>)
    requires ValidInput(n, v, sellers)
    ensures ValidOutput(count, indices, n)
    ensures CorrectSolution(v, sellers, indices)
// </vc-spec>
// <vc-code>
{
  count := 0;
  indices := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant count == |indices|
    invariant count >= 0 && count <= i
    invariant forall k :: 0 <= k < count ==> 1 <= indices[k] <= n
    invariant forall k :: 0 <= k < count - 1 ==> indices[k] < indices[k+1]
    invariant forall k :: 0 <= k < i ==> (v > Min(sellers[k]) <==> (k + 1) in indices)
  {
    if v > Min(sellers[i]) {
      count := count + 1;
      indices := indices + [i + 1];
      if count > 1 {
        assert indices[count-2] < i + 1;
      }
    }
    i := i + 1;
  }
}
// </vc-code>

