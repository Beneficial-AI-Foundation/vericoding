predicate ValidInput(n: int) {
    n >= 1
}

function MaxSum(n: int): int
    requires n >= 1
{
    n * (n - 1) / 2
}

// <vc-helpers>
function SumLoop(k: nat): int
{
  if k == 0 then 0 else SumLoop(k-1) + (k-1)
}

lemma SumFormula(k: nat)
  ensures SumLoop(k) == k * (k-1) / 2
{
  if k > 0 {
    SumFormula(k-1);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == MaxSum(n)
// </vc-spec>
// <vc-code>
{
  result := 0;
  var i: nat := 0;
  while i < n
    invariant i <= n
    invariant result == SumLoop(i)
  {
    result := result + i;
    i := i + 1;
  }
  SumFormula(n as nat);
}
// </vc-code>

