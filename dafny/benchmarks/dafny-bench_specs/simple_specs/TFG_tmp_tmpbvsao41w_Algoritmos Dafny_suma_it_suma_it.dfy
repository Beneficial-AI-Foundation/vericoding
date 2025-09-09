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


// SPEC
method suma_it(V: array<int>) returns (x: int)

// Algoritmo iterativo que calcula la
// suma de las componentes de un vector

  ensures x == suma_vector(V, 0)
{
}
