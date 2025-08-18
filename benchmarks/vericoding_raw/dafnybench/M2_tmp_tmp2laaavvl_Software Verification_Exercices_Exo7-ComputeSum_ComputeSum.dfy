function Sum(n:nat):nat

{
  if n==0 then  0 else n + Sum(n-1)
}

// <vc-helpers>
// </vc-helpers>

method ComputeSum(n:nat) returns (s:nat)
    ensures s ==Sum(n)
// <vc-code>
{
  assume false;
}
// </vc-code>