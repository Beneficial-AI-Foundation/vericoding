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
lemma CountFactorsOfTwo_is_nonnegative(n: int)
  requires n > 0
  ensures CountFactorsOfTwo(n) >= 0
  decreases n
{
  if n % 2 == 0 {
    assert n/2 > 0;
    CountFactorsOfTwo_is_nonnegative(n/2);
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
  result := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant ValidInput(a)
    invariant result >= 0
    invariant result + SumFactors(a, i) == MaxOperations(a)
    decreases |a| - i
  {
    CountFactorsOfTwo_is_nonnegative(a[i]);
    result := result + CountFactorsOfTwo(a[i]);
    i := i + 1;
  }
}
// </vc-code>

