// <vc-preamble>
function Fat(n: nat): nat
{
   if n == 0 then 1 else n * Fat(n-1)
}
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Fatorial(n:nat)  returns (r:nat)
  ensures r == Fat(n)
// </vc-spec>
// <vc-code>
{
    r := 1;
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant r == Fat(i)
    {
        i := i + 1;
        r := r * i;
    }
}
// </vc-code>
