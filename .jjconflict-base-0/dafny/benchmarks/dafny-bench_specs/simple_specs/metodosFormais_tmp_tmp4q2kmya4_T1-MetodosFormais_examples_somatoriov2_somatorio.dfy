//ATOM
function somaAteAberto(a:array<nat>, i:nat):nat
requires i <= a.Length
reads a
{
  if i ==0
  then 0
  else a[i-1] + somaAteAberto(a,i-1)
}


// SPEC

method somatorio(a:array<nat>) returns (s:nat)
ensures s == somaAteAberto(a, a.Length)
{
}
