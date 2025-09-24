// <vc-preamble>
function SomaAte(a:array<nat>, i:nat):nat
  requires 0 <= i <= a.Length
  reads a
{
    if i == 0
    then 0
    else a[i-1] + SomaAte(a,i-1)
}
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Somatorio(a:array<nat>) returns (s:nat)
  ensures s == SomaAte(a,a.Length)
// </vc-spec>
// <vc-code>
{
    var i := 0;
    s := 0;
    while i < a.Length
      invariant 0 <= i && i <= a.Length
      invariant s == SomaAte(a,i)
    {
        s := s + a[i];
        i := i + 1;
    }
}
// </vc-code>
