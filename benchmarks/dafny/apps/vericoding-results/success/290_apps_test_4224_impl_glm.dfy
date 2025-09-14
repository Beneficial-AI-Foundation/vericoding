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
lemma LemmaCountFactorsOfTwoNonNegative(n: int)
  requires n > 0
  ensures CountFactorsOfTwo(n) >= 0
{
  if n % 2 == 0 {
    LemmaCountFactorsOfTwoNonNegative(n / 2);
  }
}

lemma LemmaSumFactorsNonNegative(a: seq<int>, i: int)
  requires 0 <= i <= |a|
  requires forall j :: 0 <= j < |a| ==> a[j] > 0
  ensures SumFactors(a, i) >= 0
  decreases |a| - i
{
  if i == |a| {
  } else {
    LemmaCountFactorsOfTwoNonNegative(a[i]);
    LemmaSumFactorsNonNegative(a, i+1);
    calc {
      SumFactors(a, i);
      == CountFactorsOfTwo(a[i]) + SumFactors(a, i+1);
      >= 0 + 0;
      >= 0;
    }
  }
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
  LemmaSumFactorsNonNegative(a, 0);
  return SumFactors(a, 0);
}
// </vc-code>

