//ATOM
function SomaAte(a:array<nat>, i:nat):nat
 requires 0 <= i <= a.Length
 reads a
{
  if i == 0
  then 0
  else a[i-1] + SomaAte(a,i-1)
}


// SPEC

method Somatorio(a:array<nat>) returns (s:nat)
 ensures s == SomaAte(a,a.Length)
{
}
