// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>

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
  var current_sum: real := 0.0;
  var target := (p / 100.0) * total;
  i := -1;
  var j := 0;
  while j < A.Length
    invariant 0 <= j <= A.Length
    invariant i == j - 1
    invariant -1 <= i < A.Length
    invariant current_sum == SumUpto(A, i)
    invariant current_sum <= target
  {
    if current_sum + A[j] > target {
      return;
    }
    current_sum := current_sum + A[j];
    i := j;
    j := j + 1;
  }
}
// </vc-code>
