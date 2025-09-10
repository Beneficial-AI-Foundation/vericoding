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
lemma SumFactorsCorrect(a: seq<int>, i: int)
  requires 0 <= i <= |a|
  requires forall j :: 0 <= j < |a| ==> a[j] > 0
  ensures SumFactors(a, i) >= 0
  decreases |a| - i
{
  if i == |a| {
    // Base case
  } else {
    // Inductive case
    SumFactorsCorrect(a, i + 1);
  }
}

lemma CountFactorsNonNegative(n: int)
  requires n > 0
  ensures CountFactorsOfTwo(n) >= 0
  decreases n
{
  if n % 2 == 0 {
    CountFactorsNonNegative(n / 2);
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
    invariant result == SumFactors(a, 0) - SumFactors(a, i)
    invariant result >= 0
  {
    var temp := a[i];
    var factors := 0;
    
    while temp % 2 == 0
      invariant temp > 0
      invariant factors + CountFactorsOfTwo(temp) == CountFactorsOfTwo(a[i])
      decreases temp
    {
      temp := temp / 2;
      factors := factors + 1;
    }
    
    result := result + factors;
    i := i + 1;
  }
  
  SumFactorsCorrect(a, 0);
}
// </vc-code>

