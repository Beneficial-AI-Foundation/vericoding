// The function `SomaAte(a, i)` recursively computes the sum of the first `i` elements of array `a`. So `SomaAte(a, a.Length)` computes the sum of all elements.

// I'll implement this using a simple loop that accumulates the sum, and I'll need a loop invariant to prove that my implementation matches the specification.

// <vc-spec>
function SomaAte(a:array<nat>, i:nat):nat
  requires 0 <= i <= a.Length
  reads a
{
    if i == 0
    then 0
    else a[i-1] + SomaAte(a,i-1)
}

// <vc-helpers>
// </vc-helpers>

method Somatorio(a:array<nat>) returns (s:nat)
  ensures s == SomaAte(a,a.Length)
// </vc-spec>
// <vc-code>
{
  s := 0;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant s == SomaAte(a, i)
  {
    s := s + a[i];
    i := i + 1;
  }
}
// </vc-code>