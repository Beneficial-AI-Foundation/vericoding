function suma_aux(V : array?<int>, n : int) : int

  // suma_aux(V, n) = V[n] + V[n + 1] + ... + V[N - 1]

  requires V != null            // P_0
  requires 0 <= n <= V.Length       // Q_0

  decreases V.Length - n        // C_0

  reads V

{

  if (n == V.Length) then 0                     // Caso base:      n = N
                     else V[n] + suma_aux(V, n + 1)     // Caso recursivo: n < N

}

// <vc-helpers>
lemma suma_aux_unfold(V: array?<int>, i: int)
  requires V != null
  requires 0 <= i < V.Length
  ensures suma_aux(V,i) == V[i] + suma_aux(V,i+1)
{
  assert suma_aux(V,i) == V[i] + suma_aux(V,i+1);
}

lemma suma_aux_base(V: array?<int>)
  requires V != null
  ensures suma_aux(V, V.Length) == 0
{
  assert suma_aux(V, V.Length) == 0;
}
// </vc-helpers>

// <vc-spec>
method suma_componentes(V : array?<int>) returns (suma : int)

  requires V != null
  ensures  suma == suma_aux(V, 0)   // x = V[0] + V[1] + ... + V[N - 1]
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var s := 0;
  while i < V.Length
    invariant 0 <= i <= V.Length
    invariant s == suma_aux(V, 0) - suma_aux(V, i)
  {
    s := s + V[i];
    suma_aux_unfold(V, i);
    i := i + 1;
  }
  suma := s;
}
// </vc-code>

