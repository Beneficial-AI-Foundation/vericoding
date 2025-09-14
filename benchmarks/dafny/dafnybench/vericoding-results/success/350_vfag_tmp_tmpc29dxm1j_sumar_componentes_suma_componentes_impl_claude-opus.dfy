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
function sum_range(V: array?<int>, i: int, j: int): int
  requires V != null
  requires 0 <= i <= j <= V.Length
  decreases j - i
  reads V
{
  if i == j then 0 else V[i] + sum_range(V, i + 1, j)
}

lemma sum_range_extend(V: array?<int>, i: int, j: int)
  requires V != null
  requires 0 <= i < j <= V.Length
  ensures sum_range(V, i, j) == sum_range(V, i, j - 1) + V[j - 1]
  decreases j - i
{
  if i == j - 1 {
    assert sum_range(V, i, j) == V[i];
    assert sum_range(V, i, j - 1) == 0;
  } else {
    assert sum_range(V, i, j) == V[i] + sum_range(V, i + 1, j);
    sum_range_extend(V, i + 1, j);
  }
}

lemma sum_range_extend_right(V: array?<int>, i: int, j: int)
  requires V != null
  requires 0 <= i <= j < V.Length
  ensures sum_range(V, i, j + 1) == sum_range(V, i, j) + V[j]
  decreases j - i
{
  if i == j {
    assert sum_range(V, i, j + 1) == V[i];
    assert sum_range(V, i, j) == 0;
  } else {
    assert sum_range(V, i, j + 1) == V[i] + sum_range(V, i + 1, j + 1);
    assert sum_range(V, i, j) == V[i] + sum_range(V, i + 1, j);
    sum_range_extend_right(V, i + 1, j);
  }
}

lemma suma_decomposition(V: array?<int>, i: int, j: int)
  requires V != null
  requires 0 <= i <= j <= V.Length
  ensures suma_aux(V, i) == sum_range(V, i, j) + suma_aux(V, j)
  decreases j - i
{
  if i == j {
    assert sum_range(V, i, j) == 0;
    assert suma_aux(V, i) == suma_aux(V, j);
  } else {
    assert suma_aux(V, i) == V[i] + suma_aux(V, i + 1);
    assert sum_range(V, i, j) == V[i] + sum_range(V, i + 1, j);
    suma_decomposition(V, i + 1, j);
    assert suma_aux(V, i + 1) == sum_range(V, i + 1, j) + suma_aux(V, j);
  }
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
  
  while i < V.Length
    invariant 0 <= i <= V.Length
    invariant suma == sum_range(V, 0, i)
    invariant suma_aux(V, 0) == sum_range(V, 0, i) + suma_aux(V, i)
    decreases V.Length - i
  {
    // Maintain the decomposition invariant
    suma_decomposition(V, 0, i);
    
    // Add current element to sum
    suma := suma + V[i];
    
    // Prove that adding V[i] gives us sum_range(V, 0, i+1)
    sum_range_extend_right(V, 0, i);
    assert sum_range(V, 0, i + 1) == sum_range(V, 0, i) + V[i];
    
    i := i + 1;
    
    // Re-establish the invariant for the next iteration
    suma_decomposition(V, 0, i);
  }
  
  // At loop exit, i == V.Length
  assert i == V.Length;
  assert suma == sum_range(V, 0, V.Length);
  suma_decomposition(V, 0, V.Length);
  assert suma_aux(V, 0) == sum_range(V, 0, V.Length) + suma_aux(V, V.Length);
  assert suma_aux(V, V.Length) == 0;
  assert suma == suma_aux(V, 0);
}
// </vc-code>

