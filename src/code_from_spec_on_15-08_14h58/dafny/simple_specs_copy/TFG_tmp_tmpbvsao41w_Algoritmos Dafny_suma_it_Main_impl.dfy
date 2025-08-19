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
  decreases V.Length - n
{  
  if (n == V.Length) then 0 
  else V[n] + suma_vector(V, n + 1) 
}


//IMPL 
/* code modified by LLM (iteration 1): removed invalid text and cleaned up the method */
method Main()
{
  var v := new int[] [-1, 2, 5, -5, 8] ;
  var w := new int[] [ 1, 0, 5, 5, 8] ;
  var s1 := suma_it(v) ;
  var s2 := suma_it(w) ;

  print "La suma del vector v es: ", s1, "\n" ;
  print "La suma del vector w es: ", s2 ;
}