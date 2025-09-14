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
  var threshold := (p / 100.0) * total;
  var cumulative := 0.0;
  i := -1;

  while i < A.Length - 1
  invariant -1 <= i < A.Length
  invariant cumulative == SumUpto(A, i)
  invariant cumulative <= threshold
  {
    var next := i + 1;
    var nextSum := cumulative + A[next];
    if nextSum > threshold {
      break;
    }
    i := next;
    cumulative := nextSum;
  }

  return i;
}
// </vc-code>

// example showing that, with the original postcondition, the answer is non-unique!


// proof that, with the corrected postcondition, the answer is unique
// lemma for previous proof: when an array has strictly positive elements, the
// sums strictly increase left to right