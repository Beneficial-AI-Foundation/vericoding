// IMPL 
method suma_it(V: array<int>) returns (x: int)

// Algoritmo iterativo que calcula la
// suma de las componentes de un vector

    ensures  x == suma_vector(V, 0)
{
    x := 0;
    var i := 0;
    
    /* code modified by LLM (iteration 4): Fixed loop invariant to correctly express that x contains sum of processed elements */
    while i < V.Length
        invariant 0 <= i <= V.Length
        invariant x + suma_vector(V, i) == suma_vector(V, 0)
    {
        /* code modified by LLM (iteration 4): Added assertion to establish suma_vector decomposition */
        assert suma_vector(V, i) == V[i] + suma_vector(V, i + 1);
        
        x := x + V[i];
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 4): Added final assertion using suma_vector base case */
    assert i == V.Length;
    assert suma_vector(V, V.Length) == 0;
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

//ATOM_PLACEHOLDER_Main