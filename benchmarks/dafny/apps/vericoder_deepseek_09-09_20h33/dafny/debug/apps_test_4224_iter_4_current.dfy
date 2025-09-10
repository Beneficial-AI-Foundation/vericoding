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
lemma CountFactorsOfTwoLinear(n: int, k: int)
  requires n > 0
  requires k > 0
  requires k <= n
  ensures CountFactorsOfTwo(n) >= CountFactorsOfTwo(k)
{
  if n % 2 == 0 && k % 2 == 0 {
    CountFactorsOfTwoLinear(n / 2, k / 2);
  } else if n % 2 == 0 {
    // n is even, k is odd, so CountFactorsOfTwo(n) >= 0 = CountFactorsOfTwo(k)
    assert CountFactorsOfTwo(n) >= 1 && CountFactorsOfTwo(k) == 0;
  } else {
    // Both are odd, so CountFactorsOfTwo(n) = 0 >= 0 = CountFactorsOfTwo(k)
    assert CountFactorsOfTwo(n) == 0 && CountFactorsOfTwo(k) == 0;
  }
}

lemma SumFactorsTailRecursive(a: seq<int>, i: int, j: int, acc: int)
  requires 0 <= i <= j <= |a|
  requires forall k :: 0 <= k < |a| ==> a[k] > 0
  requires acc >= 0
  ensures SumFactors(a, i) + acc == SumFactors(a, j) + acc
  decreases j - i
{
  if i < j {
    var next_acc := acc + CountFactorsOfTwo(a[i]);
    assert SumFactors(a, i) == CountFactorsOfTwo(a[i]) + SumFactors(a, i + 1);
    SumFactorsTailRecursive(a, i + 1, j, next_acc);
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
    invariant result + SumFactors(a, i) == SumFactors(a, 0)
    invariant result >= 0
  {
    var n := a[i];
    result := result + CountFactorsOfTwo(n);
    i := i + 1;
  }
}
// </vc-code>

