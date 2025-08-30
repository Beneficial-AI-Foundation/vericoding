// ATOM 
function Sum(n:nat):nat
 
{
  if n==0 then  0 else n + Sum(n-1)
}


// SPEC 

method ComputeSum(n:nat) returns (s:nat)
    ensures s ==Sum(n)
{
}


