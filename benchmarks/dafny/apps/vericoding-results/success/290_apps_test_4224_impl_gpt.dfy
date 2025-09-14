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
lemma LemmaDiv2PosIfEven(n: int)
  requires n > 0
  requires n % 2 == 0
  ensures n / 2 > 0
{
  if n / 2 <= 0 {
    assert n == 2 * (n / 2) + n % 2;
    assert n == 2 * (n / 2);
    assert 2 * (n / 2) <= 0;
    assert n <= 0;
    assert false;
  }
}

lemma LemmaCF2NonNeg(n: int)
  requires n > 0
  ensures CountFactorsOfTwo(n) >= 0
  decreases n
{
  reveal CountFactorsOfTwo();
  if n % 2 == 0 {
    LemmaDiv2PosIfEven(n);
    LemmaCF2NonNeg(n / 2);
  } else {
  }
}

lemma LemmaSumFactorsNonNeg(a: seq<int>, i: int)
  requires 0 <= i <= |a|
  requires ValidInput(a)
  ensures SumFactors(a, i) >= 0
  decreases |a| - i
{
  reveal SumFactors();
  if i < |a| {
    assert a[i] > 0;
    LemmaCF2NonNeg(a[i]);
    LemmaSumFactorsNonNeg(a, i + 1);
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
  result := MaxOperations(a);
  reveal MaxOperations();
  LemmaSumFactorsNonNeg(a, 0);
}
// </vc-code>

