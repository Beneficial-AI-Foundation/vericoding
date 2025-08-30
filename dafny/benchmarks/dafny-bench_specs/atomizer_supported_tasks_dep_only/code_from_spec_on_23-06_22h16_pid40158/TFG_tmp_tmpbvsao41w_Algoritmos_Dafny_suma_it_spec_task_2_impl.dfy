// IMPL 
method suma_it(V: array<int>) returns (x: int)

// Algoritmo iterativo que calcula la
// suma de las componentes de un vector

    ensures  x == suma_vector(V, 0)
{
    x := 0;
    var i := 0;
    
    /* code modified by LLM (iteration 4): fixed loop invariant to correctly track partial sum */
    while i < V.Length
        invariant 0 <= i <= V.Length
        invariant x == suma_vector(V, 0) - suma_vector(V, i)
    {
        /* code modified by LLM (iteration 4): added lemma call and proper accumulation */
        if i < V.Length {
            suma_vector_split_lemma(V, 0, i);
        }
        x := x + V[i];
        i := i + 1;
    }
}

/* code modified by LLM (iteration 4): added lemma to prove sum splitting property */
lemma suma_vector_split_lemma(V: array<int>, start: nat, mid: nat)
    requires 0 <= start <= mid < V.Length
    ensures suma_vector(V, start) == suma_vector(V, start) - suma_vector(V, mid) + suma_vector(V, mid)
    ensures suma_vector(V, mid) == V[mid] + suma_vector(V, mid + 1)
{
    // The second ensures follows directly from suma_vector definition
    // The first ensures is a tautology that helps Dafny with the arithmetic
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
}