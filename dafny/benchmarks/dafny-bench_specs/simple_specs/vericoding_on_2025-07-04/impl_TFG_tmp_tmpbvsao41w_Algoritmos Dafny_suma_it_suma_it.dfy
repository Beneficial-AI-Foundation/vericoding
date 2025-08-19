//ATOM
function suma_vector(V: array<int>, n: nat): int

// x = V[n] + V[n + 1] + ... + V[N - 1]
// Funcion auxiliar para la suma de
// las componentes de un vector

  requires 0 <= n <= V.Length 
  reads V 
{  
  if (n == V.Length) then 0 
  else V[n] + suma_vector(V, n + 1) 
}

//IMPL 
method suma_it(V: array<int>) returns (x: int)

// Algoritmo iterativo que calcula la
// suma de las componentes de un vector

  ensures x == suma_vector(V, 0)
{
  x := 0;
  var i := 0;
  
  while i < V.Length
    invariant 0 <= i <= V.Length
    /* code modified by LLM (iteration 4): Corrected invariant to properly express the relationship */
    invariant x == suma_vector(V, 0) - suma_vector(V, i)
  {
    /* code modified by LLM (iteration 4): Added conditional lemma call with proper precondition check */
    if i < V.Length {
      suma_vector_split_lemma(V, i);
    }
    x := x + V[i];
    i := i + 1;
  }
}

/* code modified by LLM (iteration 4): Added helper lemma to prove the split property of suma_vector */
lemma suma_vector_split_lemma(V: array<int>, i: nat)
  requires 0 <= i < V.Length
  reads V
  ensures suma_vector(V, i) == V[i] + suma_vector(V, i + 1)
{
  // This follows directly from the definition of suma_vector when i < V.Length
}