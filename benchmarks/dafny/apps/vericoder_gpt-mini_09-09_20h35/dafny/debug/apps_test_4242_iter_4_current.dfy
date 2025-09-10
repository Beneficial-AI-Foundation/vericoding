function CommonDivisors(A: int, B: int): set<int>
  requires A > 0 && B > 0
{
  set d | 1 <= d <= A && A % d == 0 && B % d == 0
}

predicate ValidInput(A: int, B: int, K: int)
{
  A > 0 && B > 0 && K >= 1 && |CommonDivisors(A, B)| >= K
}

predicate IsKthLargestCommonDivisor(A: int, B: int, K: int, result: int)
  requires ValidInput(A, B, K)
{
  result > 0 &&
  A % result == 0 && B % result == 0 &&
  result in CommonDivisors(A, B) &&
  |set d | d in CommonDivisors(A, B) && d > result| == K - 1
}

// <vc-helpers>
method BuildDivisors(A: int, B: int) returns (cur: seq<int>)
  requires A > 0 && B > 0
  ensures set cur == CommonDivisors(A, B)
  ensures forall i :: 0 <= i + 1 < |cur| ==> cur[i] > cur[i + 1]
{
  cur := [];
  var i := A;
  while i >= 1
    invariant 0 <= i <= A
    invariant forall j :: 0 <= j < |cur| ==> 1 <= cur[j] <= A && A % cur[j] == 0 && B % cur[j] == 0
    invariant forall j :: 0 <= j + 1 < |cur| ==> cur[j] > cur[j + 1]
    invariant forall d :: i < d <= A && A % d == 0 && B % d == 0 ==> d in set cur
    decreases i
  {
    if A % i == 0 && B % i == 0 {
      cur := cur + [i];
    }
    i := i - 1;
  }
  assert forall d :: d in set cur ==> 1 <= d <= A && A % d == 0 && B % d == 0;
  assert set cur == CommonDivisors(A, B);
}

lemma SeqStrictDecreasingCardinality(s: seq<int>, n: int)
  requires 0 <= n <= |s|
  requires forall i, j :: 0 <= i < j < n ==> s[i] != s[j]
  ensures | (set s[0..n]) | == n
{
  // Every element in the slice corresponds to some index
  assert forall x :: x in (set s[0..n]) ==> exists i :: 0 <= i < n && s[i] == x;
  // Every index in range yields an element in the set
  assert forall i :: 0 <= i < n ==> s[i] in (set s[0..n]);
  // Distinctness hypothesis already provided
  assert forall i, j :: 0 <= i < j < n ==> s[i] != s[j];
  // Conclude the cardinality equality
  assert | (set s[0..n]) | == n;
}

lemma CountGreaterByIndex(A: int, B: int, cur: seq<int>, idx: int)
  requires 0 <= idx < |cur|
  requires set cur == CommonDivisors(A, B)
  requires forall i :: 0 <= i + 1 < |cur| ==> cur[i] > cur[i + 1]
  ensures | (set d | d in CommonDivisors(A, B) && d > cur[idx]) | == idx
{
  var result := cur[idx];
  // Elements of cur are exactly the common divisors
  assert set cur == CommonDivisors(A, B);
  // Any common divisor greater than result appears in cur and must be at an index < idx
  assert forall d :: d in CommonDivisors(A, B) && d > result ==>
         (exists j :: 0 <= j < idx && cur[j] == d);
  // Conversely, any cur[j] with j < idx is a common divisor greater than result
  assert forall j :: 0 <= j < idx ==> cur[j] in CommonDivisors(A, B) && cur[j] > result;
  // The former characterization yields equality of the two sets:
  assert (set d | d in CommonDivisors(A, B) && d > result) ==
         (set d | exists j :: 0 <= j < idx && cur[j] == d);
  // That latter set is exactly set cur[0..idx]
  assert (set d | exists j :: 0 <= j < idx && cur[j] == d) == (set cur[0..idx]);
  // Now show |set cur[0..idx]| == idx using distinctness of elements up to idx
  assert forall i, j :: 0 <= i < j < idx ==> cur[i] != cur[j];
  SeqStrictDecreasingCardinality(cur, idx);
  assert | (set cur[0..idx]) | == idx;
  // Combine to conclude the desired cardinality
  assert | (set d | d in CommonDivisors(A, B) && d > result) | == idx;
}
// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int, K: int) returns (result: int)
  requires ValidInput(A, B, K)
  ensures IsKthLargestCommonDivisor(A, B, K, result)
// </vc-spec>
// <vc-code>
{
  var cur := BuildDivisors(A, B);
  // cur contains exactly the common divisors and is strictly decreasing
  assert set cur == CommonDivisors(A, B);
  assert forall i :: 0 <= i + 1 < |cur| ==> cur[i] > cur[i + 1];
  // From strict decrease we have pairwise distinctness
  assert forall i, j :: 0 <= i < j < |cur| ==> cur[i] != cur[j];
  // Relate cardinalities of set cur and CommonDivisors
  SeqStrictDecreasingCardinality(cur, |cur|);
  assert | (set cur[0..|cur|]) | == |cur|;
  assert | (CommonDivisors(A, B)) | == |cur|;
  // K is at most the number of common divisors by ValidInput, so index is in range
  var idx := K - 1;
  assert 0 <= idx < |cur|;
  CountGreaterByIndex(A, B, cur, idx);
  result := cur[idx];
}
// </vc-code>

