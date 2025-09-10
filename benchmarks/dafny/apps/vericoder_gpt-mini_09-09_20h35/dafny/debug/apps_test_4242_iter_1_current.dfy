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
  ensures set cur[..] == CommonDivisors(A, B)
  ensures forall i :: 0 <= i + 1 < |cur| ==> cur[i] > cur[i + 1]
{
  cur := [];
  var i := A;
  while i >= 1
    invariant 0 <= i <= A
    invariant forall j :: 0 <= j < |cur| ==> 1 <= cur[j] <= A && A % cur[j] == 0 && B % cur[j] == 0
    invariant forall j :: 0 <= j + 1 < |cur| ==> cur[j] > cur[j + 1]
    invariant forall d :: i < d <= A && A % d == 0 && B % d == 0 ==> d in set cur[..]
    decreases i
  {
    if A % i == 0 && B % i == 0 {
      cur := cur + [i];
    }
    i := i - 1;
  }
  // At this point i == 0, so by the invariant all divisors in 1..A are in cur and
  // by the other invariants every element of cur is a common divisor and cur is strictly decreasing.
  assert forall d :: d in set cur[..] ==> 1 <= d <= A && A % d == 0 && B % d == 0;
  // Show set cur[..] == CommonDivisors(A,B)
  // From the invariant with i == 0 we have that any d with 0 < d <= A and dividing A and B is in cur.
  assert set cur[..] == CommonDivisors(A, B);
}

lemma SeqStrictDecreasingCardinality<T>(s: seq<T>, n: int)
  requires 0 <= n <= |s|
  requires forall i, j :: 0 <= i < j < n ==> s[i] != s[j]
  ensures |set s[..n]| == n
{
  // show <= n:
  assert forall x :: x in set s[..n] ==> exists i :: 0 <= i < n && s[i] == x;
  // Thus the set has at most n elements.
  // show >= n:
  assert forall i :: 0 <= i < n ==> s[i] in set s[..n];
  // And by the distinctness hypothesis the elements s[0..n-1] are pairwise distinct,
  // hence the set contains at least n distinct elements.
  // Conclude equality of cardinalities.
  reveal |set s[..n]|;
  // These facts are sufficient for Dafny to conclude |set s[..n]| == n.
}

lemma CountGreaterByIndex(A: int, B: int, cur: seq<int>, idx: int)
  requires 0 <= idx < |cur|
  requires set cur[..] == CommonDivisors(A, B)
  requires forall i :: 0 <= i + 1 < |cur| ==> cur[i] > cur[i + 1]
  ensures |set d | d in CommonDivisors(A, B) && d > cur[idx]| == idx
{
  var result := cur[idx];
  // Show the set of common divisors greater than result equals the set of cur[j] for j < idx
  assert set d | d in CommonDivisors(A, B) && d > result|
         == set d | exists j :: 0 <= j < idx && cur[j] == d;
  // That latter set is exactly set cur[..idx]
  assert set d | exists j :: 0 <= j < idx && cur[j] == d == set cur[..idx];
  // Now show |set cur[..idx]| == idx using strict decreasing property
  // First, elements cur[0..idx-1] are pairwise distinct because cur is strictly decreasing.
  assert forall i, j :: 0 <= i < j < idx ==> cur[i] != cur[j];
  SeqStrictDecreasingCardinality(cur, idx);
  // The lemma ensures |set cur[..idx]| == idx, therefore
  assert |set cur[..idx]| == idx;
  // Combine with equalities above to conclude the desired cardinality
  assert |set d | d in CommonDivisors(A, B) && d > result| == idx;
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
  result := cur[K - 1];
  // result divides A and B and is positive follows from BuildDivisors properties
  assert result > 0 && A % result == 0 && B % result == 0;
  // Use lemma to show exactly K-1 common divisors are greater than result
  CountGreaterByIndex(A, B, cur, K - 1);
  return;
}
// </vc-code>

