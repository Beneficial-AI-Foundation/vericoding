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


// example showing that, with the original postcondition, the answer is non-unique!

// <vc-helpers>
lemma SumUptoIncreasing(A: array<real>, i: int)
  requires forall j | 0 <= j < A.Length :: A[j] > 0.0
  requires 0 <= i < A.Length
  ensures SumUpto(A, i-1) < SumUpto(A, i)
{
  if i == 0 {
    assert SumUpto(A, -1) == 0.0;
    assert SumUpto(A, 0) == A[0] + SumUpto(A, -1) == A[0];
    assert A[0] > 0.0;
  } else {
    SumUptoIncreasing(A, i-1);
    assert SumUpto(A, i) == A[i] + SumUpto(A, i-1);
    assert A[i] > 0.0;
  }
}

lemma SumUptoPositive(A: array<real>, i: int)
  requires forall j | 0 <= j < A.Length :: A[j] > 0.0
  requires 0 <= i < A.Length
  ensures SumUpto(A, i) > 0.0
{
  if i == 0 {
    assert SumUpto(A, 0) == A[0];
  } else {
    SumUptoPositive(A, i-1);
    assert SumUpto(A, i) == A[i] + SumUpto(A, i-1);
  }
}

lemma SumUptoCalc(A: array<real>)
  requires A.Length == 3
  requires A[0] == 10.0 && A[1] == 20.0 && A[2] == 30.0
  ensures SumUpto(A, -1) == 0.0
  ensures SumUpto(A, 0) == 10.0
  ensures SumUpto(A, 1) == 30.0
  ensures SumUpto(A, 2) == 60.0
{
  // These follow from the definition of SumUpto
}

lemma SumUptoSpecificCalc(A: array<real>)
  requires A.Length == 3
  requires A[0] == 10.0 && A[1] == 20.0 && A[2] == 30.0
  ensures SumUpto(A, 2) == 60.0
  ensures 30.0 <= 30.0
  ensures 60.0 >= 30.0
{
  SumUptoCalc(A);
}
// </vc-helpers>

// <vc-spec>
method PercentileNonUniqueAnswer() returns (p: real, A: array<real>, total: real, i1: int, i2: int)
  ensures forall i | 0 <= i < A.Length :: A[i] > 0.0
  ensures 0.0 <= p <= 100.0
  ensures total == Sum(A)
  ensures total > 0.0

  ensures -1 <= i1 < A.Length
  ensures SumUpto(A, i1) <= (p/100.0) * total
  ensures i1+1 < A.Length ==> SumUpto(A, i1+1) >= (p/100.0) * total

  ensures -1 <= i2 < A.Length
  ensures SumUpto(A, i2) <= (p/100.0) * total
  ensures i2+1 < A.Length ==> SumUpto(A, i2+1) >= (p/100.0) * total

  ensures i1 != i2
// </vc-spec>
// <vc-code>
{
  A := new real[3];
  A[0] := 10.0;
  A[1] := 20.0;
  A[2] := 30.0;
  
  p := 50.0;
  total := Sum(A);
  
  SumUptoPositive(A, A.Length-1);
  SumUptoCalc(A);
  SumUptoSpecificCalc(A);
  
  var target := (p/100.0) * total;
  
  assert target == 30.0;
  assert SumUpto(A, 0) == 10.0;
  assert SumUpto(A, 1) == 30.0;
  assert SumUpto(A, 2) == 60.0;
  
  i1 := 0;
  i2 := 1;
}
// </vc-code>

// proof that, with the corrected postcondition, the answer is unique
// lemma for previous proof: when an array has strictly positive elements, the
// sums strictly increase left to right