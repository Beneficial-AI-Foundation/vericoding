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
lemma suma_unfold_lt(V: array?<int>, i: int)
  requires V != null
  requires 0 <= i < V.Length
  ensures suma_aux(V, i) == V[i] + suma_aux(V, i + 1)
{
}

lemma suma_at_length(V: array?<int>)
  requires V != null
  ensures suma_aux(V, V.Length) == 0
{
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
  suma := 0;
  ghost var total := suma_aux(V, 0);
  while i < V.Length
    invariant V != null
    invariant 0 <= i <= V.Length
    invariant suma == total - suma_aux(V, i)
    decreases V.Length - i
  {
    var i0 := i;
    suma_unfold_lt(V, i0);
    suma := suma + V[i0];
    i := i0 + 1;
  }
  assert i == V.Length;
  suma_at_length(V);
  assert suma == total - suma_aux(V, V.Length);
  assert suma_aux(V, V.Length) == 0;
  assert suma == total;
  assert suma == suma_aux(V, 0);
}
// </vc-code>

