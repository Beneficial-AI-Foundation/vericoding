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
  suma := 0;
  var i := 0;
  while i < V.Length
    invariant 0 <= i <= V.Length
    invariant suma_aux(V, 0) == suma + suma_aux(V, i)
    decreases V.Length - i
  {
    suma := suma + V[i];
    i := i + 1;
  }
}
// </vc-code>
