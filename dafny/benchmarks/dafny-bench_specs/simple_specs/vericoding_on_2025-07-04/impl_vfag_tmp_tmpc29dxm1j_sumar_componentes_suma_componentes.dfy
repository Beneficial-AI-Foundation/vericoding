//ATOM
function suma_aux(V : array?<int>, n : int) : int
 // suma_aux(V, n) = V[n] + V[n + 1] + ... + V[N - 1]
 requires V != null			// P_0
 requires 0 <= n <= V.Length		// Q_0
 reads V
{
 if (n == V.Length) then 0 					// Caso base:   n = N
           else V[n] + suma_aux(V, n + 1)		// Caso recursivo: n < N
}

//IMPL 
method suma_componentes(V : array?<int>) returns (suma : int)
 requires V != null
 ensures suma == suma_aux(V, 0)	// x = V[0] + V[1] + ... + V[N - 1]
{
    suma := 0;
    var i := 0;
    while i < V.Length
        invariant 0 <= i <= V.Length
        invariant suma + suma_aux(V, i) == suma_aux(V, 0)
    {
        /* code modified by LLM (iteration 4): Added assertion to establish the recursive definition of suma_aux */
        assert i < V.Length;
        assert suma_aux(V, i) == V[i] + suma_aux(V, i + 1);
        
        /* code modified by LLM (iteration 4): Store old values for proof */
        var old_suma := suma;
        var old_i := i;
        
        suma := suma + V[i];
        i := i + 1;
        
        /* code modified by LLM (iteration 4): Assert that the invariant is maintained after the updates */
        assert suma == old_suma + V[old_i];
        assert i == old_i + 1;
        assert suma + suma_aux(V, i) == old_suma + V[old_i] + suma_aux(V, old_i + 1);
        assert old_suma + V[old_i] + suma_aux(V, old_i + 1) == old_suma + suma_aux(V, old_i);
        assert old_suma + suma_aux(V, old_i) == suma_aux(V, 0);
    }
}