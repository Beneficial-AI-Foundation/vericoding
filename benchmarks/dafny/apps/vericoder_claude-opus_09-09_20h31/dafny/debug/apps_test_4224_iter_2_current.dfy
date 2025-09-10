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
lemma SumFactorsPartial(a: seq<int>, i: int, j: int)
  requires ValidInput(a)
  requires 0 <= i <= j <= |a|
  ensures SumFactors(a, i) == SumFactors(a[i..j], 0) + SumFactors(a, j)
  decreases j - i
{
  if i == j {
    assert a[i..j] == [];
    assert SumFactors(a[i..j], 0) == 0;
  } else {
    assert a[i..j][0] == a[i];
    SumFactorsPartial(a, i+1, j);
    assert a[i+1..j] == a[i..j][1..];
  }
}

lemma SumFactorsAccumulation(a: seq<int>, i: int, acc: int)
  requires ValidInput(a)
  requires 0 <= i <= |a|
  ensures SumFactors(a, 0) == acc + SumFactors(a, i) <==> SumFactors(a, 0) == acc + SumFactors(a[i..], 0)
{
  assert a[i..] == if i == |a| then [] else a[i..];
  if i < |a| {
    SumFactorsPartial(a, i, |a|);
    assert a[i..|a|] == a[i..];
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
  var total := 0;
  var i := 0;
  
  while i < |a|
    invariant 0 <= i <= |a|
    invariant total == SumFactors(a, 0) - SumFactors(a, i)
  {
    var n := a[i];
    var count := 0;
    
    while n % 2 == 0
      invariant n > 0
      invariant count + CountFactorsOfTwo(n) == CountFactorsOfTwo(a[i])
      decreases n
    {
      n := n / 2;
      count := count + 1;
    }
    
    total := total + count;
    i := i + 1;
  }
  
  result := total;
}
// </vc-code>

