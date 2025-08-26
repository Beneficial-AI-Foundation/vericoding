function SumUpto(A: array<real>, end: int): real
  requires -1 <= end < A.Length
  reads A
{
  if end == -1 then 0.0
  else
    A[end] + SumUpto(A, end-1)
}

function Sum(A: array<real>): real
  reads A
{
  SumUpto(A, A.Length-1)
}

// <vc-helpers>
lemma SumUptoMonotonic(A: array<real>, end1: int, end2: int)
  requires forall i | 0 <= i < A.Length :: A[i] > 0.0
  requires -1 <= end1 <= end2 < A.Length
  ensures SumUpto(A, end1) <= SumUpto(A, end2)
{
  if end1 == end2 {
    // Base case: they're equal
  } else if end1 == -1 {
    // SumUpto(A, -1) = 0.0, and SumUpto(A, end2) >= 0 since all elements are positive
  } else {
    // end1 < end2, so we can use induction
    SumUptoMonotonic(A, end1, end2-1);
    // SumUpto(A, end1) <= SumUpto(A, end2-1)
    // SumUpto(A, end2) = A[end2] + SumUpto(A, end2-1)
    // Since A[end2] > 0.0, we have SumUpto(A, end2-1) < SumUpto(A, end2)
  }
}

lemma SumUptoAdditive(A: array<real>, end: int)
  requires 0 <= end < A.Length
  ensures SumUpto(A, end) == SumUpto(A, end-1) + A[end]
{
  // This follows directly from the definition
}
// </vc-helpers>

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
  var threshold := (p/100.0) * total;
  i := -1;
  var currentSum := 0.0;
  
  while i+1 < A.Length && currentSum + A[i+1] <= threshold
    invariant -1 <= i < A.Length
    invariant currentSum == SumUpto(A, i)
    invariant currentSum <= threshold
    decreases A.Length - i - 1
  {
    i := i + 1;
    currentSum := currentSum + A[i];
    
    // Help Dafny understand the relationship
    if i == 0 {
      assert SumUpto(A, 0) == A[0];
    } else {
      SumUptoAdditive(A, i);
    }
  }
  
  // At this point, either:
  // 1. i+1 >= A.Length (we've reached the end), or
  // 2. currentSum + A[i+1] > threshold (adding next element would exceed threshold)
}
// </vc-code>

// example showing that, with the original postcondition, the answer is non-unique!


// proof that, with the corrected postcondition, the answer is unique
lemma PercentileUniqueAnswer(p: real, A: array<real>, total: real, i1: int, i2: int)
  requires forall i | 0 <= i < A.Length :: A[i] > 0.0
  requires 0.0 <= p <= 100.0
  requires total == Sum(A)
  requires total > 0.0

  requires -1 <= i1 < A.Length
  requires SumUpto(A, i1) <= (p/100.0) * total
  requires i1+1 < A.Length ==> SumUpto(A, i1+1) > (p/100.0) * total

  requires -1 <= i2 < A.Length
  requires SumUpto(A, i2) <= (p/100.0) * total
  requires i2+1 < A.Length ==> SumUpto(A, i2+1) > (p/100.0) * total

  decreases if i2 < i1 then 1 else 0  // wlog i1 <= i2
    ensures i1 == i2
{
  assume false;

  if i1+1< i2 {
    SumUpto_increase(A, i1+1, i2);
  }
}
// lemma for previous proof: when an array has strictly positive elements, the
// sums strictly increase left to right
lemma SumUpto_increase(A: array<real>, end1: int, end2: int)
  requires forall i | 0 <= i < A.Length :: A[i] > 0.0
  requires -1 <= end1 < A.Length
  requires -1 <= end2 < A.Length
  requires end1 < end2
  ensures SumUpto(A, end1) < SumUpto(A, end2)
{}