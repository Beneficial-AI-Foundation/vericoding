//IMPL mergesort
method mergesort(V : array?<int>, c : int, f : int) 
    requires V != null
    requires c >= 0 && f <= V.Length
    /* code modified by LLM (iteration 2): added precondition to ensure c <= f */
    requires c <= f
    modifies V
    /* code modified by LLM (iteration 1): added decreases clause for termination */
    decreases f - c
{
    if c < f - 1 {
        var m := (c + f) / 2;
        /* code modified by LLM (iteration 1): added assertion to help with verification */
        assert c < m < f;
        mergesort(V, c, m);
        mergesort(V, m, f);
        mezclar(V, c, m, f);
    }
}

//IMPL mezclar
method mezclar(V: array?<int>, c : int, m : int, f : int)
    requires V != null
    requires c <= m <= f
    requires 0 <= c <= V.Length
    requires 0 <= m <= V.Length
    requires 0 <= f <= V.Length
    modifies V
{
    if c >= f {
        return;
    }
    
    var temp := new int[f - c];
    var i := c;
    var j := m;
    var k := 0;
    
    // Merge the two halves
    while i < m && j < f
        invariant c <= i <= m
        invariant m <= j <= f
        invariant k == (i - c) + (j - m)
        invariant 0 <= k <= temp.Length
        invariant temp.Length == f - c
    {
        /* code modified by LLM (iteration 1): added bounds check assertions for clarity */
        assert i < V.Length && j < V.Length;
        assert k < temp.Length;
        if V[i] <= V[j] {
            temp[k] := V[i];
            i := i + 1;
        } else {
            temp[k] := V[j];
            j := j + 1;
        }
        k := k + 1;
    }
    
    // Copy remaining elements from left half
    while i < m
        invariant c <= i <= m
        /* code modified by LLM (iteration 2): fixed invariant for j */
        invariant j == f
        invariant k == (i - c) + (j - m)
        invariant 0 <= k <= temp.Length
        invariant temp.Length == f - c
    {
        /* code modified by LLM (iteration 1): added bounds check assertion */
        assert i < V.Length && k < temp.Length;
        temp[k] := V[i];
        i := i + 1;
        k := k + 1;
    }
    
    // Copy remaining elements from right half
    while j < f
        /* code modified by LLM (iteration 2): fixed invariant for i */
        invariant i == m
        invariant m <= j <= f
        invariant k == (i - c) + (j - m)
        invariant 0 <= k <= temp.Length
        invariant temp.Length == f - c
    {
        /* code modified by LLM (iteration 1): added bounds check assertion */
        assert j < V.Length && k < temp.Length;
        temp[k] := V[j];
        j := j + 1;
        k := k + 1;
    }
    
    // Copy back to original array
    k := 0;
    while k < f - c
        invariant 0 <= k <= f - c
        invariant temp.Length == f - c
        /* code modified by LLM (iteration 1): added invariant for array bounds */
        invariant c + k <= V.Length
    {
        /* code modified by LLM (iteration 1): added bounds check assertion */
        assert c + k < V.Length && k < temp.Length;
        V[c + k] := temp[k];
        k := k + 1;
    }
}