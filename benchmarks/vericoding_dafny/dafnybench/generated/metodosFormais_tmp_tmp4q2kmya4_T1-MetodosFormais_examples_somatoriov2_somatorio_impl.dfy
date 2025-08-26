// <vc-spec>
function somaAteAberto(a:array<nat>, i:nat):nat
requires i <= a.Length
reads a
{
    if i ==0
    then 0
    else a[i-1] + somaAteAberto(a,i-1)
}

// <vc-helpers>
// </vc-helpers>

method somatorio(a:array<nat>) returns (s:nat)
ensures s == somaAteAberto(a, a.Length)
// </vc-spec>
// <vc-code>
{
  s := 0;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant s == somaAteAberto(a, i)
  {
    s := s + a[i];
    i := i + 1;
  }
}
// </vc-code>