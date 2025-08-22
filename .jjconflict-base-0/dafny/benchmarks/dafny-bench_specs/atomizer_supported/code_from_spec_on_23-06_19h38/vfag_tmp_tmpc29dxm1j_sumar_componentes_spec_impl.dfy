// ATOM 
function suma_aux(V : array?<int>, n : int) : int
  // suma_aux(V, n) = V[n] + V[n + 1] + ... + V[N - 1]
  requires V != null			// P_0
  requires 0 <= n <= V.Length		// Q_0
  reads V
{
  if (n == V.Length) then 0 					// Caso base:      n = N
                     else V[n] + suma_aux(V, n + 1)		// Caso recursivo: n < N
}

/* code modified by LLM (iteration 1): Added helper lemma to prove suma_aux properties */
lemma suma_aux_step(V: array?<int>, i: int)
  requires V != null
  requires 0 <= i < V.Length
  ensures suma_aux(V, i) == V[i] + suma_aux(V, i + 1)
{
  // This follows directly from the definition of suma_aux
}

// IMPL 
method suma_componentes(V : array?<int>) returns (suma : int)
  requires V != null
  ensures  suma == suma_aux(V, 0)	// x = V[0] + V[1] + ... + V[N - 1]
{
  /* code modified by LLM (iteration 1): Fixed loop body to maintain invariant with lemma call */
  suma := 0;
  var i := 0;
  
  while i < V.Length
    invariant 0 <= i <= V.Length
    invariant suma + suma_aux(V, i) == suma_aux(V, 0)
  {
    suma_aux_step(V, i);
    suma := suma + V[i];
    i := i + 1;
  }
}