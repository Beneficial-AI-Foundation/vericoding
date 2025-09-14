predicate ValidInput(a: seq<int>) {
  forall i :: 0 <= i < |a| ==> a[i] > 0
}

function CountFactorsOfTwo(n: int): int
  requires n > 0
  decreases n
{
  if n % 2 == 0 then 1 + CountFactorsOfTwo(n / 2)
  else 0
}

function SumFactors(a: seq<int>, i: int): int
  requires 0 <= i <= |a|
  requires forall j :: 0 <= j < |a| ==> a[j] > 0
  decreases |a| - i
{
  if i == |a| then 0
  else CountFactorsOfTwo(a[i]) + SumFactors(a, i + 1)
}

function MaxOperations(a: seq<int>): int
  requires ValidInput(a)
{
  SumFactors(a, 0)
}

// <vc-helpers>
lemma CountFactorsNonNeg(n: int)
  requires n > 0
  ensures CountFactorsOfTwo(n) >= 0
  decreases n
{
  if n % 2 == 0 {
    // n is even and > 0, so n >= 2 and n/2 > 0
    CountFactorsNonNeg(n / 2);
  } else {
    // odd case: CountFactorsOfTwo(n) == 0
  }
}

lemma SumFactorsNonNeg(a: seq<int>, i: int)
  requires 0 <= i <= |a|
  requires ValidInput(a)
  ensures SumFactors(a, i) >= 0
  decreases |a| - i
{
  if i == |a| {
    // SumFactors(a, |a|) == 0
  } else {
    CountFactorsNonNeg(a[i]);
    SumFactorsNonNeg(a, i + 1);
  }
}

lemma MaxOperationsNonNeg(a: seq<int>)
  requires ValidInput(a)
  ensures MaxOperations(a) >= 0
{
  SumFactorsNonNeg(a, 0);
}
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>) returns (result: int)
  requires ValidInput(a)
  ensures result >= 0
  ensures result == MaxOperations(a)
// </vc-spec>
// <vc-code>
{
  result := MaxOperations(a);
  MaxOperationsNonNeg(a);
}
// </vc-code>

