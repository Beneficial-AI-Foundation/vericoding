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

//IMPL suma_it
method suma_it(V: array<int>) returns (x: int)

// Algoritmo iterativo que calcula la
// suma de las componentes de un vector

  ensures x == suma_vector(V, 0)
{
  x := 0;
  var i := 0;
  while i < V.Length
    invariant 0 <= i <= V.Length
    invariant x + suma_vector(V, i) == suma_vector(V, 0)
  {
    /* code modified by LLM (iteration 2): establish recursive relationship before updating x */
    assert suma_vector(V, i) == V[i] + suma_vector(V, i + 1);
    x := x + V[i];
    /* code modified by LLM (iteration 2): prove invariant holds after updates using substitution */
    assert x == (x - V[i]) + V[i];
    assert x == suma_vector(V, 0) - suma_vector(V, i) + V[i];
    assert x == suma_vector(V, 0) - (V[i] + suma_vector(V, i + 1)) + V[i];
    assert x == suma_vector(V, 0) - suma_vector(V, i + 1);
    i := i + 1;
    assert x + suma_vector(V, i) == suma_vector(V, 0);
  }
}