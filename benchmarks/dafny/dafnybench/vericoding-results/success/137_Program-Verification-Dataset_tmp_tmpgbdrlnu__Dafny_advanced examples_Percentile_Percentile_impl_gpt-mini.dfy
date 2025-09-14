// Sum of elements of A from indices 0 to end.
// end is inclusive! (not James's normal way of thinking!!)
function SumUpto(A: array<real>, end: int): real
  requires -1 <= end < A.Length
  reads A
{
  if end == -1 then
    0.0
  else
    A[end] + SumUpto(A, end-1)
}

function Sum(A: array<real>): real
  reads A
{
  SumUpto(A, A.Length-1)
}

// <vc-helpers>
lemma SumsIncrease(A: array<real>, m: int, n: int)
  requires 0 <= m < n < A.Length
  requires forall i | 0 <= i < A.Length :: A[i] > 0.0
  ensures SumUpto(A, m) < SumUpto(A, n)
  decreases n - m
{
  if m + 1 == n {
    // SumUpto(A,n) == SumUpto(A,n-1) + A[n], and SumUpto(A,m) == SumUpto(A,n-1)
    assert SumUpto(A, n) == SumUpto(A, n-1) + A[n];
    assert SumUpto(A, m) == SumUpto(A, n-1);
    assert A[n] > 0.0;
    assert SumUpto(A, m) < SumUpto(A, n);
  } else {
    SumsIncrease(A, m, n-1);
    // SumUpto(A,n) == SumUpto(A,n-1) + A[n]
    assert SumUpto(A, n) == SumUpto(A, n-1) + A[n];
    assert A[n] > 0.0;
    assert SumUpto(A, n-1) < SumUpto(A, n);
    assert SumUpto(A, m) < SumUpto(A, n);
  }
}
// </vc-helpers>

// <vc-spec>
method Percentile(p: real, A: array<real>, total: real) returns (i: int)
  requires forall i | 0 <= i < A.Length :: A[i] > 0.0
  requires 0.0 <= p <= 100.0
  requires total == Sum(A)
  requires total > 0.0
  ensures -1 <= i < A.Length
  ensures SumUpto(A, i) <= (p/100.0) * total
  ensures i+1 < A.Length ==> SumUpto(A, i+1) > (p/100.0) * total
// </vc-spec>
// <vc-code>
{
  var target := (p / 100.0) * total;
  var s := 0.0;
  var k := 0;
  i := -1;
  while k < A.Length && s + A[k] <= target
    invariant 0 <= k <= A.Length
    invariant -1 <= i < A.Length
    invariant i + 1 == k
    invariant s == SumUpto(A, i)
    invariant s <= target
  {
    s := s + A[k];
    i := k;
    k := k + 1;
  }
  // s == SumUpto(A,i) and s <= target prove first postcondition
  assert s == SumUpto(A, i);
  assert s <= target;
  // if there is a next element, show its prefix sum exceeds target
  if i + 1 < A.Length {
    // k == i+1 and loop condition failed, so s + A[k] > target
    assert i + 1 == k;
    assert s + A[k] > target;
    assert SumUpto(A, i + 1) == SumUpto(A, i) + A[i + 1];
    assert s + A[k] == SumUpto(A, i + 1);
    assert SumUpto(A, i + 1) > target;
  }
}
// </vc-code>

// example showing that, with the original postcondition, the answer is non-unique!


// proof that, with the corrected postcondition, the answer is unique
// lemma for previous proof: when an array has strictly positive elements, the
// sums strictly increase left to right