//ATOM
method suma_it(V: array<int>) returns (x: int)

// Algoritmo iterativo que calcula la
// suma de las componentes de un vector

  ensures x == suma_vector(V, 0)
{
  x := 0;
  var i := 0;
  
  while i < V.Length
    invariant 0 <= i <= V.Length
    invariant x == suma_vector(V, 0) - suma_vector(V, i)
  {
    x := x + V[i];
    i := i + 1;
  }
}

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
method Main()
{
  /* code modified by LLM (iteration 1): Fixed array initialization and added proper variable declarations */
  var v := new int[5];
  v[0] := -1; v[1] := 2; v[2] := 5; v[3] := -5; v[4] := 8;
  
  var w := new int[5];
  w[0] := 1; w[1] := 0; w[2] := 5; w[3] := 5; w[4] := 8;
  
  var s1 := suma_it(v);
  var s2 := suma_it(w);

  print "La suma del vector v es: ", s1, "\n";
  print "La suma del vector w es: ", s2;
}