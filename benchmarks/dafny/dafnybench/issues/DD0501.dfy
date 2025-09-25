// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method suma_it(V: array<int>) returns (x: int)

// Algoritmo iterativo que calcula la
// suma de las componentes de un vector

    ensures  x == suma_vector(V, 0)
// </vc-spec>
// <vc-code>
{
    var n := V.Length ;
        x := 0 ;
    while (n != 0)
        invariant 0 <= n <= V.Length && x == suma_vector(V, n)
        decreases n
    {
        x := x + V[n - 1] ;
        n := n - 1 ;
    }
}
// </vc-code>

function suma_vector(V: array<int>, n: nat): int

// x = V[n] + V[n + 1] + ... + V[N - 1]
// Funcion auxiliar para la suma de
// las componentes de un vector

    requires 0 <= n <= V.Length  
    decreases V.Length - n  
    reads V  
{    
    if (n == V.Length) then 0 
    else V[n] + suma_vector(V, n + 1)  
}