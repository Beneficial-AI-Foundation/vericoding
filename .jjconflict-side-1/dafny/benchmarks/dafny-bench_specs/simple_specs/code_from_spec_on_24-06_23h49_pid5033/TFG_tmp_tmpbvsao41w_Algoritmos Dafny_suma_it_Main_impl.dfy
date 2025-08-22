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
    /* code modified by LLM (iteration 4): Fixed loop invariant to correctly state that x equals sum from 0 to i */
    invariant x == suma_vector_range(V, 0, i)
  {
    /* code modified by LLM (iteration 4): Added lemma call to maintain invariant */
    suma_vector_split_lemma(V, 0, i);
    x := x + V[i];
    i := i + 1;
  }
  /* code modified by LLM (iteration 4): Added final lemma call to prove postcondition */
  suma_vector_range_full_lemma(V);
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

/* code modified by LLM (iteration 4): Added helper function for sum over a range */
function suma_vector_range(V: array<int>, start: nat, end: nat): int
  requires 0 <= start <= end <= V.Length
  reads V
{
  if start == end then 0
  else V[start] + suma_vector_range(V, start + 1, end)
}

/* code modified by LLM (iteration 4): Added lemma to relate suma_vector_range with suma_vector */
lemma suma_vector_split_lemma(V: array<int>, start: nat, mid: nat)
  requires 0 <= start <= mid < V.Length
  ensures suma_vector_range(V, start, mid + 1) == suma_vector_range(V, start, mid) + V[mid]
{
  if start == mid {
    // Base case: suma_vector_range(V, mid, mid) == 0
  } else {
    // Recursive case
    suma_vector_split_lemma(V, start + 1, mid);
  }
}

/* code modified by LLM (iteration 4): Added lemma to prove suma_vector_range(V, 0, V.Length) == suma_vector(V, 0) */
lemma suma_vector_range_full_lemma(V: array<int>)
  ensures suma_vector_range(V, 0, V.Length) == suma_vector(V, 0)
{
  suma_vector_range_equals_suma_vector(V, 0, V.Length);
}

/* code modified by LLM (iteration 4): Added helper lemma for the equivalence */
lemma suma_vector_range_equals_suma_vector(V: array<int>, start: nat, end: nat)
  requires 0 <= start <= end <= V.Length
  ensures suma_vector_range(V, start, end) == (if start == V.Length then 0 else suma_vector(V, start) - suma_vector(V, end))
{
  if start == end {
    // Both are 0
  } else if start == V.Length {
    // Both are 0
  } else {
    // Inductive case
    suma_vector_range_equals_suma_vector(V, start + 1, end);
  }
}

//IMPL
method Main()
{
  /* code modified by LLM (iteration 4): Fixed array initialization - use proper Dafny array creation syntax */
  var v := new int[5];
  v[0] := -1; v[1] := 2; v[2] := 5; v[3] := -5; v[4] := 8;
  
  var w := new int[5];
  w[0] := 1; w[1] := 0; w[2] := 5; w[3] := 5; w[4] := 8;
  
  var s1 := suma_it(v);
  var s2 := suma_it(w);

  print "La suma del vector v es: ", s1, "\n";
  print "La suma del vector w es: ", s2;
}