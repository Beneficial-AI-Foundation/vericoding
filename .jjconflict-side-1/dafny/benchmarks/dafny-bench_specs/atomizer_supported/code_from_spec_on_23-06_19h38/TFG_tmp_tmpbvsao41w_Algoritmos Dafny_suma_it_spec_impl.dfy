// IMPL 
method suma_it(V: array<int>) returns (x: int)

// Algoritmo iterativo que calcula la
// suma de las componentes de un vector

    ensures  x == suma_vector(V, 0)
{
    x := 0;
    var i := 0;
    
    /* code modified by LLM (iteration 4): Fixed loop invariant to properly track accumulated sum */
    while i < V.Length
        invariant 0 <= i <= V.Length
        invariant x == suma_vector(V, 0) - suma_vector(V, i)
    {
        /* code modified by LLM (iteration 4): Use lemma to establish recursive property before update */
        suma_vector_lemma(V, i);
        
        x := x + V[i];
        i := i + 1;
    }
}

/* code modified by LLM (iteration 4): Helper lemma to prove recursive decomposition property */
lemma suma_vector_lemma(V: array<int>, n: nat)
    requires 0 <= n < V.Length
    ensures suma_vector(V, n) == V[n] + suma_vector(V, n + 1)
{
    // This follows directly from the recursive definition of suma_vector
}

// ATOM 
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

// IMPL 
method Main()
{
    var arr := new int[3];
    arr[0] := 1;
    arr[1] := 2;
    arr[2] := 3;
    var result := suma_it(arr);
    print result;
}