// <vc-preamble>
function suma_aux(V : array?<int>, n : int) : int

  requires V != null
  requires 0 <= n <= V.Length

  decreases V.Length - n

  reads V

{

  if (n == V.Length) then 0
                     else V[n] + suma_aux(V, n + 1)

}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method suma_componentes(V : array?<int>) returns (suma : int)

  requires V != null
  ensures  suma == suma_aux(V, 0)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
