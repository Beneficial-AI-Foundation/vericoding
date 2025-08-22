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

/* code modified by LLM (iteration 3): Added lemma to help with sum relationship */
lemma suma_aux_step(V: array?<int>, i: int)
    requires V != null
    requires 0 <= i < V.Length
    ensures suma_aux(V, i) == V[i] + suma_aux(V, i + 1)
{
    // This follows directly from the definition of suma_aux
}

/* code modified by LLM (iteration 3): Added lemma for partial sum relationship */
lemma suma_aux_partial(V: array?<int>, current_sum: int, i: int)
    requires V != null
    requires 0 <= i <= V.Length
    requires current_sum == suma_aux(V, 0) - suma_aux(V, i)
    ensures current_sum + suma_aux(V, i) == suma_aux(V, 0)
{
    // This is a simple arithmetic fact
}

//IMPL suma_componentes
method suma_componentes(V : array?<int>) returns (suma : int)

 requires V != null
 ensures suma == suma_aux(V, 0)	// x = V[0] + V[1] + ... + V[N - 1]
 
{
    suma := 0;
    var i := 0;
    
    /* code modified by LLM (iteration 3): Use invariant that suma equals sum of processed elements */
    while i < V.Length
        invariant 0 <= i <= V.Length
        invariant suma == suma_aux(V, 0) - suma_aux(V, i)
    {
        /* code modified by LLM (iteration 3): Use lemma to establish suma_aux relationship */
        suma_aux_step(V, i);
        assert suma_aux(V, i) == V[i] + suma_aux(V, i + 1);
        
        /* code modified by LLM (iteration 3): Update suma and verify invariant maintenance */
        var old_suma := suma;
        suma := suma + V[i];
        i := i + 1;
        
        /* code modified by LLM (iteration 3): Verify new invariant holds */
        assert old_suma == suma_aux(V, 0) - suma_aux(V, i - 1);
        assert suma_aux(V, i - 1) == V[i - 1] + suma_aux(V, i);
        assert suma == old_suma + V[i - 1];
        assert suma == (suma_aux(V, 0) - suma_aux(V, i - 1)) + V[i - 1];
        assert suma == suma_aux(V, 0) - (suma_aux(V, i - 1) - V[i - 1]);
        assert suma == suma_aux(V, 0) - suma_aux(V, i);
    }
    
    /* code modified by LLM (iteration 3): Final verification */
    assert i == V.Length;
    assert suma_aux(V, V.Length) == 0;
    assert suma == suma_aux(V, 0) - 0;
    assert suma == suma_aux(V, 0);
}