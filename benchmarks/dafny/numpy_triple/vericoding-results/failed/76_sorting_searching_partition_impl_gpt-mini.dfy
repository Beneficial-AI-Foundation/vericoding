// <vc-preamble>
// Ghost predicate to check if a sequence is sorted in non-decreasing order
ghost predicate IsSorted(s: seq<real>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Ghost predicate to check if two sequences are permutations of each other
ghost predicate IsPermutation(s1: seq<real>, s2: seq<real>)
{
    |s1| == |s2| &&
    forall x :: Count(s1, x) == Count(s2, x)
}

// Ghost function to count occurrences of an element in a sequence
ghost function Count(s: seq<real>, x: real): nat
{
    if |s| == 0 then 0
    else (if s[0] == x then 1 else 0) + Count(s[1..], x)
}

// Ghost function that returns a sorted version of the input sequence
ghost function SortedVersion(s: seq<real>): seq<real>

// Ghost predicate that ensures SortedVersion produces a valid sorted permutation
ghost predicate SortedVersionValid(s: seq<real>)
{
    var sorted := SortedVersion(s);
    IsSorted(sorted) && IsPermutation(s, sorted)
}

// Axiom that SortedVersion always produces a valid result
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Min, RemoveOne, and lemmas to reason about Count and equality of sorted permutations */
ghost function Min(s: seq<real>): real
  requires |s| > 0
  ensures Count(s, result) > 0
  ensures forall x :: Count(s, x) > 0 ==> result <= x
{
  if |s| == 1 then s[0] else var m := Min(s[1..]); if s[0] <= m then s[0] else m
}

/* helper modified by LLM (iteration 3): remove one occurrence of x from sequence s */
ghost function RemoveOne(s: seq<real>, x: real): seq<real>
  requires Count(s, x) > 0
  ensures |RemoveOne(s, x)| + 1 == |s|
  ensures Count(RemoveOne(s, x), x) + 1 == Count(s, x)
  ensures forall y :: y != x ==> Count(RemoveOne(s, x), y) == Count(s, y)
  decreases |s|
{
  if s[0] == x then s[1..] else [s[0]] + RemoveOne(s[1..], x)
}

/* helper modified by LLM (iteration 3): concatenation preserves Count */
lemma CountConcat(s: seq<real>, t: seq<real>, x: real)
  ensures Count(s + t, x) == Count(s, x) + Count(t, x)
  decreases |s|
{
  if |s| == 0 {
  } else {
    CountConcat(s[1..], t, x);
  }
}

/* helper modified by LLM (iteration 3): tail count relation */
lemma CountTail(s: seq<real>, y: real)
  requires |s| > 0
  ensures Count(s[1..], y) + (if s[0] == y then 1 else 0) == Count(s, y)
  decreases |s|
{
  if s[0] == y {
  } else {
    CountTail(s[1..], y);
  }
}

/* helper modified by LLM (iteration 3): existence of index for positive Count */
lemma CountPosImpliesIndex(s: seq<real>, x: real)
  requires Count(s, x) > 0
  ensures exists i :: 0 <= i < |s| && s[i] == x
  decreases |s|
{
  if |s| == 0 {
    assert false;
  }
  if s[0] == x {
    assert 0 <= 0 < |s| && s[0] == x;
  } else {
    // Then Count(s[1..], x) > 0
    CountPosImpliesIndex(s[1..], x);
    var j :| 0 <= j < |s[1..]| && s[1..][j] == x;
    var i := j + 1;
    assert 0 <= i < |s| && s[i] == x;
  }
}

/* helper modified by LLM (iteration 3): two sorted permutations of the same multiset are identical */
lemma SortedPermutationsEqual(s: seq<real>, a: seq<real>, b: seq<real>)
  requires |s| == |a|
  requires |a| == |b|
  requires IsSorted(a)
  requires IsSorted(b)
  requires IsPermutation(s, a)
  requires IsPermutation(s, b)
  ensures a == b
  decreases |s|
{
  if |s| == 0 {
    return;
  }

  var m := Min(s);
  // m occurs in s
  assert Count(s, m) > 0;
  // From IsPermutation(s,a) we have Count(a,m) > 0
  assert Count(a, m) == Count(s, m);
  assert Count(a, m) > 0;
  // From Count positive, there is an index in a with value m
  CountPosImpliesIndex(a, m);
  // Show a[0] == m
  // m <= every element of s, so m <= every element of a
  assert forall i :: 0 <= i < |a| ==> m <= a[i];
  // From IsSorted(a) a[0] <= a[i] for all i, and since some a[i] == m we get a[0] <= m
  // Conclude a[0] == m
  assert m <= a[0];
  // There is some i with a[i] == m, so a[0] <= m
  assert a[0] <= m;
  assert a[0] == m;

  // Similarly for b
  assert Count(b, m) == Count(s, m) && Count(b, m) > 0;
  CountPosImpliesIndex(b, m);
  assert forall i :: 0 <= i < |b| ==> m <= b[i];
  assert m <= b[0];
  assert b[0] <= m;
  assert b[0] == m;

  // Remove one occurrence of m from s and from a and b's head
  var s1 := RemoveOne(s, m);
  var a1 := a[1..];
  var b1 := b[1..];

  // Show lengths and sortedness for tails
  assert |s1| + 1 == |s|;
  assert |a1| + 1 == |a|;
  assert |b1| + 1 == |b|;
  assert IsSorted(a1);
  assert IsSorted(b1);

  // Show permutations for tails using counts
  // For any y, Count(a1,y) + (if y == m then 1 else 0) == Count(a,y)
  CountTail(a, m);
  CountTail(b, m);
  // From RemoveOne ensures Count(s1, y) == Count(s, y) - (if y==m then 1 else 0)
  // So Count(s1, y) == Count(a1, y) for all y
  assert forall y :: Count(s1, y) == Count(a1, y);
  assert forall y :: Count(s1, y) == Count(b1, y);

  // Recurse
  SortedPermutationsEqual(s1, a1, b1);
}

// </vc-helpers>

// <vc-spec>
lemma {:axiom} SortedVersionIsValid(s: seq<real>)
    ensures SortedVersionValid(s)

/**
 * Partitions an array around the k-th element.
 * Returns a rearranged copy where the k-th element is in its correct sorted position,
 * with smaller elements before it and equal/greater elements after it.
 */
method Partition(arr: seq<real>, kth: int) returns (result: seq<real>)
    requires 0 <= kth < |arr|
    ensures |result| == |arr|
    // All elements before kth position are <= the kth element
    ensures forall i :: 0 <= i < kth ==> result[i] <= result[kth]
    // All elements after kth position are >= the kth element
    ensures forall i :: kth < i < |result| ==> result[i] >= result[kth]
    // The k-th element is in its correct sorted position
    ensures SortedVersionValid(arr) ==> result[kth] == SortedVersion(arr)[kth]
    // The result is a permutation of the original array
    ensures IsPermutation(arr, result)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): selection-based partition ensuring invariants and invoking helpers for verification */
  var rem := arr;
  result := [];
  while |rem| > 0
    invariant |result| + |rem| == |arr|
    invariant forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
    invariant forall ri, rj :: 0 <= ri < |result| && 0 <= rj < |rem| ==> result[ri] <= rem[rj]
    invariant forall v :: Count(result, v) + Count(rem, v) == Count(arr, v)
    decreases |rem|
  {
    var minIdx := 0;
    var j := 1;
    while j < |rem|
      invariant 1 <= |rem| ==> 0 <= minIdx < |rem|
      invariant 1 <= |rem| ==> 1 <= j <= |rem|
      invariant 1 <= |rem| ==> forall k :: 0 <= k < j ==> rem[minIdx] <= rem[k]
      decreases |rem| - j
    {
      if rem[j] < rem[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }
    // pick the minimum element
    var picked := rem[minIdx];
    // update result and rem
    var oldRem := rem;
    result := result + [picked];
    rem := oldRem[..minIdx] + oldRem[minIdx+1..];

    // help the verifier with Count relations
    // Count of picked increased in result by 1 and decreased in rem by 1
    ghost CountConcat(result[..|result|-1], [picked], picked);
    ghost CountConcat(oldRem[..minIdx], oldRem[minIdx+1..], picked);
    // No runtime effect; these lemma/ghost calls help establish the invariants
  }

  // If the input had a canonical sorted version, prove that our result matches it at each position
  ghost {
    if SortedVersionValid(arr) {
      SortedPermutationsEqual(arr, result, SortedVersion(arr));
    }
  }
}

// </vc-code>
