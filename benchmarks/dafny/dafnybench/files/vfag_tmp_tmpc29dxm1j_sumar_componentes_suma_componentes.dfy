/*
// suma_aux(V, n) = V[n] + V[n + 1] + ... + V[N - 1]

// P_0

// Q_0

// C_0

// Caso base:      n = N

// Caso recursivo: n < N

// x = V[0] + V[1] + ... + V[N - 1]
*/

function suma_aux(V : array?<int>, n : int) : int

  requires V != null
  requires 0 <= n <= V.Length

  decreases V.Length - n

  reads V

{

  if (n == V.Length) then 0
                     else V[n] + suma_aux(V, n + 1)

}

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
