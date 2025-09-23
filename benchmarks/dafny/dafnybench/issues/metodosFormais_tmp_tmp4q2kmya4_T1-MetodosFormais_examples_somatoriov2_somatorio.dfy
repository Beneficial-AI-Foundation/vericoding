// <vc-preamble>
function somaAteAberto(a:array<nat>, i:nat):nat
requires i <= a.Length
reads a
{
    if i ==0
    then 0
    else a[i-1] + somaAteAberto(a,i-1)
}
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method somatorio(a:array<nat>) returns (s:nat)
ensures s == somaAteAberto(a, a.Length)
// </vc-spec>
// <vc-code>
{
    s := 0;
    for i:= 0 to a.Length
    invariant s == somaAteAberto(a,i)
    {
        s := s + a[i];
    }
}
// </vc-code>
